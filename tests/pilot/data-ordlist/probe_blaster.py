#!/usr/bin/env python3
"""Explore Blaster on a fresh translation without changing the proof gate."""

from pathlib import Path
import subprocess
import tempfile


REPO = Path(__file__).resolve().parents[3]
SOURCE = REPO / "tests/pilot/data-ordlist/OrderedPilot.hs"
GENERIC_PROBE = """
theorem blaster_idempotent_probe {α : Type} (cmp : α → α → Ordering)
    (x : α) (xs : List α) (hself : cmp x x = Ordering.eq) :
    insertSetBy cmp x (insertSetBy cmp x xs) = insertSetBy cmp x xs := by
  induction xs with
  | nil => blaster (timeout: 5)
  | cons y ys ih =>
      cases h : cmp x y with
      | lt => blaster (timeout: 5)
      | eq => blaster (timeout: 5)
      | gt => blaster (timeout: 5)
#print axioms blaster_idempotent_probe
"""
MACHINE_PROBE = """
theorem blaster_int64_probe (x : Int64) : memberInt x [x] = true := by
  blaster (timeout: 5)
#print axioms blaster_int64_probe
"""


def lean_probe(model: str, probe: str, path: Path) -> subprocess.CompletedProcess[str]:
    marker = "end OrderedPilot"
    before, separator, after = model.rpartition(marker)
    if not separator or after.strip():
        raise ValueError("Expected the translated model to end with OrderedPilot")
    path.write_text(before + probe + "\n" + marker + "\n")
    return subprocess.run(["lake", "env", "lean", str(path)], cwd=REPO,
                          text=True, capture_output=True, check=False, timeout=120)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="ordlist-blaster-") as tmp:
        directory = Path(tmp)
        generated = directory / "OrderedPilot.lean"
        subprocess.run([str(REPO / "transpile.sh"), str(SOURCE), str(generated),
                        "--semantics", "conservative"], cwd=REPO, check=True,
                       timeout=600)
        model = generated.read_text()

        generic = lean_probe(model, GENERIC_PROBE, directory / "GenericProbe.lean")
        print("Generic induction/case-split probe:")
        print(generic.stdout + generic.stderr)
        if generic.returncode or "Blaster.Tactic.blasterProven" not in generic.stdout:
            raise SystemExit("Generic Blaster probe did not produce the expected SMT result")

        machine = lean_probe(model, MACHINE_PROBE, directory / "Int64Probe.lean")
        print("Direct Int64 probe:")
        print(machine.stdout + machine.stderr)
        if machine.returncode:
            print("Blaster cannot discharge this machine-Int goal at the pinned revision.")
        else:
            print("Blaster discharged the machine-Int goal; inspect its axiom report.")


if __name__ == "__main__":
    main()
