"""Private build artifacts for one GHC Core -> Lean run (stdlib only)."""

from __future__ import annotations

import ast
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

REPO = Path(__file__).resolve().parents[1]


class PipelineError(Exception):
    def __init__(self, phase: str, message: str, *, status: str = "error"):
        super().__init__(message)
        self.phase = phase
        self.status = status


def tool_env() -> dict[str, str]:
    env = os.environ.copy()
    home = Path.home()
    bins = [home / p for p in (".ghcup/bin", ".cabal/bin", ".elan/bin", ".local/bin")]
    env["PATH"] = os.pathsep.join(map(str, bins)) + os.pathsep + env.get("PATH", "")
    # Never inherit another pipeline's sidecars, import graph, or package env.
    for key in ("LEAN_SPEC_DIR", "GHC_DECL_DUMP_DIR", "EXT_TYPES_MANIFEST",
                "NEWTYPE_EXPORTS_OUT", "LEAN_IMPORTS", "GHCCORE_AUDIT",
                "GHCCORE_SEMANTICS", "GHCCORE_INT_BITS", "GHC_ENVIRONMENT", "LEAN_PATH"):
        env.pop(key, None)
    env["GHC_ENVIRONMENT"] = "-"
    return env


def run(args: list[str], *, cwd: Path, env: dict[str, str], deadline: float,
        phase: str) -> subprocess.CompletedProcess[str]:
    remaining = deadline - time.monotonic()
    if not math.isfinite(remaining):
        raise PipelineError(phase, "Time limit must be finite")
    if remaining <= 0:
        raise PipelineError(phase, "Run exceeded its time limit", status="timeout")
    if env.get("GHCCORE_PROGRESS") == "1":
        labels = {"setup": "Checking toolchain", "discover": "Discovering Haskell imports",
                  "ghc": "Building Haskell with GHC (Cabal)", "manifest": "Reading type declarations",
                  "shim": "Decoding GHC Core", "transpile": "Translating Core to Lean",
                  "lean": "Checking Lean proofs and auditing axioms"}
        message = labels.get(phase, phase)
        if phase == "lean":
            message += ": " + Path(args[-1]).name
        print("GHCCORE_PROGRESS:" + json.dumps({"phase": phase, "message": message}),
              file=sys.stderr, flush=True)
    try:
        proc = subprocess.Popen(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True, start_new_session=True)
    except OSError as exc:
        raise PipelineError(phase, str(exc)) from exc
    try:
        stdout, stderr = proc.communicate(timeout=remaining)
    except (subprocess.TimeoutExpired, KeyboardInterrupt) as exc:
        # Cabal/GHC/Lean/Z3 descendants must not outlive a cancelled run.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        if isinstance(exc, KeyboardInterrupt):
            raise
        raise PipelineError(phase, "Run exceeded its time limit", status="timeout") from exc
    return subprocess.CompletedProcess(args, proc.returncode, stdout, stderr)


def require(result: subprocess.CompletedProcess[str], phase: str) -> str:
    if result.returncode:
        raise PipelineError(phase, result.stderr + result.stdout)
    return result.stdout


def parse_ghc_target(output: str) -> dict[str, object]:
    try:
        info = dict(ast.literal_eval(output.strip()))
        word_bytes = int(info["target word size"])
        platform = info["target platform string"]
    except (SyntaxError, ValueError, TypeError, KeyError) as exc:
        raise PipelineError("setup", "Could not read GHC target information") from exc
    if word_bytes <= 0:
        raise PipelineError("setup", "GHC reported an invalid target word size")
    return {"platform": platform, "intBits": word_bytes * 8}


def ghc_target(env: dict[str, str], deadline: float) -> dict[str, object]:
    output = require(run(["ghc-9.2.7", "--info"], cwd=REPO, env=env,
                         deadline=deadline, phase="setup"), "setup")
    return parse_ghc_target(output)


def require_supported_target(target: dict[str, object], semantics: str) -> None:
    if semantics == "conservative" and target["intBits"] != 64:
        raise PipelineError(
            "setup",
            f"Conservative Int semantics currently support 64-bit GHC targets; got {target['intBits']}-bit",
            status="unsupported")


def private_lean_environment(work: Path, env: dict[str, str], deadline: float
                             ) -> tuple[Path, dict[str, str]]:
    """Return a Lean environment that sees private Generated modules only."""
    lean_env = json.loads(require(run(
        ["lake", "env", "python3", "-c",
         "import json,os; print(json.dumps(dict(os.environ)))"],
        cwd=REPO, env=env, deadline=deadline, phase="setup"), "setup"))
    root = work / "lean"
    package = root / "GhcCoreToLean"
    package.mkdir(parents=True, exist_ok=True)
    support = REPO / ".lake/build/lib/lean/GhcCoreToLean"
    if not support.is_dir():
        raise PipelineError("setup", "Build GhcCoreToLean before running the pipeline")
    # A private GhcCoreToLean directory shadows the installed package as a
    # unit. Link its support artifacts while deliberately excluding every
    # shared Generated output from earlier runs.
    for artifact in support.iterdir():
        if artifact.name != "Generated":
            destination = package / artifact.name
            if not destination.exists():
                destination.symlink_to(artifact)
    lean_env["LEAN_PATH"] = str(root) + os.pathsep + lean_env.get("LEAN_PATH", "")
    return root, lean_env


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cancel_on_termination() -> None:
    """Route SIGTERM through the same process-group cleanup as Ctrl-C."""
    def interrupted(_signum, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)


def discover(source: Path, env: dict[str, str], deadline: float) -> list[dict]:
    output = require(run(["python3", str(REPO / "scripts/transpile_graph.py"),
                          "discover", str(source)], cwd=REPO, env=env,
                         deadline=deadline, phase="discover"), "discover")
    modules = []
    for line in output.splitlines():
        name, path, deps = line.split("\t")
        modules.append({"module": name, "source": path,
                        "dependencies": deps.split(",") if deps else []})
    if not modules:
        raise PipelineError("discover", "No local modules discovered")
    return modules


def transpile(source: Path, work: Path, env: dict[str, str], deadline: float,
              *, semantics: str = "approximate", audit: bool = False,
              target: dict[str, object] | None = None) -> list[dict]:
    """Write the entire module graph under work/lean; publish nothing externally."""
    target = target or ghc_target(env, deadline)
    require_supported_target(target, semantics)
    env = {**env, "GHCCORE_INT_BITS": str(target["intBits"])}
    modules = discover(source, env, deadline)
    stage = work / "haskell"
    stage.mkdir()
    decls = stage / ".decls"
    specs = stage / ".leanspecs"
    decls.mkdir()
    specs.mkdir()
    for module in modules:
        original = Path(module["source"])
        content = original.read_bytes()
        module["sha256"] = hashlib.sha256(content).hexdigest()
        dest = stage / (module["module"].replace(".", "/") + ".hs")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(content)
    (stage / "transpile-sandbox.cabal").write_text(
        "cabal-version: 2.4\nname: transpile-sandbox\nversion: 0.1.0.0\n"
        "library\n  exposed-modules: " + ", ".join(m["module"] for m in modules) + "\n"
        "  build-depends: base, ghc-dump-core, decl-plugin, lean-spec, spec-plugin\n"
        "  default-language: Haskell2010\n  hs-source-dirs: .\n"
        "  ghc-options: -fplugin GhcDump.Plugin -fplugin GhcDeclDump -fplugin GhcSpecDump\n")
    packages = [REPO / "shim" / name for name in ("decl-plugin", "lean-spec", "spec-plugin")]
    (stage / "cabal.project").write_text(
        "with-compiler: ghc-9.2.7\npackages:\n  .\n"
        + "".join("  " + json.dumps(str(p)) + "\n" for p in packages))
    (stage / "cabal.project.freeze").write_bytes(
        (REPO / "shim/cabal.project.freeze").read_bytes())
    env = {**env, "GHC_DECL_DUMP_DIR": str(decls), "LEAN_SPEC_DIR": str(specs),
           "GHCCORE_SEMANTICS": semantics, "GHCCORE_AUDIT": "1" if audit else "0"}
    require(run(["cabal", "build"], cwd=stage, env=env, deadline=deadline, phase="ghc"), "ghc")

    shim = require(run(["cabal", "list-bin", "exe:ghc-core-shim"], cwd=REPO / "shim",
                       env=env, deadline=deadline, phase="setup"), "setup").strip()
    compiler = REPO / ".lake/build/bin/ghccoretolean"
    if not Path(shim).is_file() or not compiler.is_file():
        raise PipelineError("setup", "Build the shim and ghccoretolean first (see README)")

    manifest = stage / "types.tsv"
    manifest.write_text(require(run(
        ["python3", str(REPO / "scripts/transpile_graph.py"), "manifest", str(decls)]
        + [m["module"] for m in modules], cwd=REPO, env=env, deadline=deadline,
        phase="manifest"), "manifest"))
    env["EXT_TYPES_MANIFEST"] = str(manifest)
    for module in modules:
        name = module["module"]
        suffix = name.replace(".", "/") + ".pass-0000.cbor"
        dumps = [p for p in (stage / "dist-newstyle").rglob("*.pass-0000.cbor")
                 if p.as_posix().endswith("/" + suffix)]
        sidecar = decls / (name + ".decls.json")
        if len(dumps) != 1 or not sidecar.is_file():
            raise PipelineError("ghc", f"Expected one Core dump and a declaration sidecar for {name}")
        core = stage / (name + ".json")
        core.write_text(require(run([shim, str(dumps[0]), "--decls", str(sidecar)],
                                    cwd=stage, env=env, deadline=deadline, phase="shim"), "shim"))
        output = work / "lean/GhcCoreToLean/Generated" / (name.replace(".", "/") + ".lean")
        output.parent.mkdir(parents=True, exist_ok=True)
        exports = decls / (name + ".newtypes.tsv")
        module_env = {**env, "NEWTYPE_EXPORTS_OUT": str(exports),
                      "LEAN_IMPORTS": " ".join("GhcCoreToLean.Generated." + d
                                               for d in module["dependencies"])}
        result = run([str(compiler), str(core), str(output), name], cwd=stage,
                     env=module_env, deadline=deadline, phase="transpile")
        if result.returncode:
            raise PipelineError("transpile", result.stderr + result.stdout, status="unsupported")
        if semantics == "conservative" and result.stderr.strip():
            raise PipelineError("transpile", "Conservative verification refuses translation warnings:\n"
                                + result.stderr, status="unsupported")
        module["warnings"] = result.stderr
        if exports.exists():
            with manifest.open("a") as handle:
                handle.write(exports.read_text())
        map_path = Path(str(output) + ".map.json")
        mapping = json.loads(map_path.read_text())
        mapping["haskellPath"] = module["source"]
        mapping["sourceSha256"] = module["sha256"]
        map_path.write_text(json.dumps(mapping, indent=2) + "\n")
        module["lean"] = str(output)
        module["map"] = mapping
    return modules


def ensure_unchanged(modules: list[dict]) -> None:
    for module in modules:
        path = Path(module["source"])
        if not path.is_file() or digest(path) != module["sha256"]:
            raise PipelineError("snapshot", f"Source changed during the run: {path}", status="stale")


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as handle:
        temp = Path(handle.name)
        handle.write(content)
    try:
        os.replace(temp, path)
    finally:
        temp.unlink(missing_ok=True)


def export(modules: list[dict], output: Path | None) -> None:
    # Export is a convenience for manual Lean work. Verification itself never
    # reads these shared outputs. Lock concurrent exports and replace each file
    # atomically, after every module translated successfully.
    import fcntl
    lock = REPO / ".lake/ghccore-export.lock"
    lock.parent.mkdir(exist_ok=True)
    with lock.open("w") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        ensure_unchanged(modules)
        for module in modules:
            dest = (output if module is modules[-1] and output else
                    REPO / "GhcCoreToLean/Generated" / (module["module"].replace(".", "/") + ".lean"))
            mapping = {**module["map"], "leanPath": str(dest)}
            atomic_write(dest, Path(module["lean"]).read_text())
            atomic_write(Path(str(dest) + ".map.json"), json.dumps(mapping, indent=2) + "\n")
            print(f"wrote {dest}")
