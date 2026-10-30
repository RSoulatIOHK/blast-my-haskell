import json
import io
from contextlib import redirect_stderr
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from pipeline import (PipelineError, digest, ensure_unchanged, parse_ghc_target,
                      require_supported_target, run, tool_env)
from verify import accepted, aggregate, module_result, proof_status


class ResultTests(unittest.TestCase):
    def setUp(self):
        self.module = {"module": "Test", "source": "/tmp/Test.hs", "sha256": "abc",
                       "warnings": "", "map": {"blocks": [{"hs": [1, 3], "lean": [10, 12]}]}}

    def audit(self, entries):
        return json.dumps({"severity": "information", "data": "GHCCORE_AUDIT:" + json.dumps(entries)})

    def test_trust_is_explicit(self):
        self.assertEqual(proof_status(["propext", "Classical.choice", "Quot.sound"]), "proved")
        self.assertEqual(proof_status(["Blaster.Tactic.blasterProven"]), "smt_valid")
        self.assertFalse(accepted("smt_valid", False))
        self.assertTrue(accepted("smt_valid", True))
        self.assertEqual(proof_status(["sorryAx", "Blaster.Tactic.blasterProven"]), "admitted")
        self.assertFalse(accepted("admitted", True))
        self.assertEqual(proof_status(["User.assumption"]), "assumed")
        self.assertFalse(accepted("assumed", True))

    def test_silence_and_missing_audit_are_not_success(self):
        self.assertEqual(module_result(self.module, "", "", 0)["status"], "error")
        self.assertEqual(module_result(self.module, self.audit([]), "", 0)["status"], "no_theorem")

    def test_every_theorem_in_a_block_is_audited(self):
        entries = [{"name": "first", "line": 10, "axioms": []},
                   {"name": "second", "line": 12, "axioms": ["sorryAx"]}]
        result = module_result(self.module, self.audit(entries), "", 0)
        self.assertEqual(result["status"], "admitted")
        self.assertEqual(len(result["properties"][0]["theorems"]), 2)

    def test_errors_override_audit_and_success_messages(self):
        text = self.audit([{"name": "first", "line": 10, "axioms": []}])
        text += "\n" + json.dumps({"severity": "error", "data": "unknown identifier"})
        self.assertEqual(module_result(self.module, text, "", 0)["status"], "error")
        self.assertEqual(module_result(self.module, text, "", 1)["status"], "error")

    def test_refutation_is_distinct_from_compile_error(self):
        text = json.dumps({"severity": "error", "data": "Goal was falsified (see counterexample above)"})
        self.assertEqual(module_result(self.module, text, "", 1)["status"], "refuted")

    def test_duplicate_audit_is_protocol_error(self):
        text = self.audit([]) + "\n" + self.audit([])
        self.assertEqual(module_result(self.module, text, "", 0)["status"], "error")

    def test_no_properties_is_not_success(self):
        self.assertEqual(aggregate([]), "no_properties")
        self.assertFalse(accepted("no_properties", True))


class PipelineTests(unittest.TestCase):
    def test_ghc_target_word_size_is_recorded_in_bits(self):
        target = parse_ghc_target(
            '[("target platform string", "x86_64-test"), ("target word size", "8")]')
        self.assertEqual(target, {"platform": "x86_64-test", "intBits": 64})

    def test_invalid_ghc_target_is_a_setup_error(self):
        with self.assertRaises(PipelineError) as raised:
            parse_ghc_target('[("target word size", "unknown")]')
        self.assertEqual(raised.exception.phase, "setup")

    def test_conservative_mode_refuses_non_64_bit_int(self):
        with self.assertRaises(PipelineError) as raised:
            require_supported_target({"platform": "i386-test", "intBits": 32}, "conservative")
        self.assertEqual(raised.exception.status, "unsupported")
        require_supported_target({"platform": "i386-test", "intBits": 32}, "approximate")

    def test_progress_is_opt_in_and_does_not_contaminate_stdout(self):
        for enabled in [False, True]:
            output = io.StringIO()
            env = tool_env()
            env["GHCCORE_PROGRESS"] = "1" if enabled else "0"
            with redirect_stderr(output):
                result = run([sys.executable, "-c", "print('result')"], cwd=Path.cwd(),
                             env=env, deadline=time.monotonic() + 10, phase="ghc")
            self.assertEqual(result.stdout, "result\n")
            if enabled:
                prefix, payload = output.getvalue().split(":", 1)
                self.assertEqual(prefix, "GHCCORE_PROGRESS")
                self.assertEqual(json.loads(payload)["phase"], "ghc")
            else:
                self.assertEqual(output.getvalue(), "")

    def test_changed_source_invalidates_result(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / "Input.hs"
            source.write_text("before")
            modules = [{"source": str(source), "sha256": digest(source)}]
            ensure_unchanged(modules)
            source.write_text("after")
            with self.assertRaises(PipelineError) as raised:
                ensure_unchanged(modules)
            self.assertEqual(raised.exception.status, "stale")

    def test_subprocess_has_wall_clock_limit(self):
        with self.assertRaises(PipelineError) as raised:
            run([sys.executable, "-c", "import time; time.sleep(20)"], cwd=Path.cwd(),
                env=tool_env(), deadline=time.monotonic() + 0.1, phase="test")
        self.assertEqual(raised.exception.status, "timeout")

    def test_invalid_time_limit_never_starts_a_subprocess(self):
        for deadline in [float("nan"), float("inf")]:
            with self.assertRaises(PipelineError):
                run(["nonexistent-command"], cwd=Path.cwd(), env=tool_env(),
                    deadline=deadline, phase="test")


if __name__ == "__main__":
    unittest.main()
