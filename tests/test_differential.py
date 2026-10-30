"""Checks for typed list inputs to the GHC/Lean differential oracle."""

import json
import hashlib
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from differential import expand_cases, haskell_runner, lean_runner, load_config


class ListInputTests(unittest.TestCase):
    def config(self, vectors):
        return {
            "schemaVersion": 1,
            "seed": 1,
            "suites": [{
                "module": "Pilot",
                "source": "Pilot.hs",
                "operations": [{"function": "insert", "arguments": ["int64", "int64-list"],
                                "result": "int64-list", "vectors": vectors}],
            }],
        }

    def load(self, config):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "config.json"
            path.write_text(json.dumps(config))
            return load_config(path)

    def test_empty_negative_and_boundary_lists_render_for_both_runners(self):
        config = self.load(self.config([[0, []], [-1, [-1, 0]],
                                        [0, [-(1 << 63), (1 << 63) - 1]]]))
        cases = expand_cases(config, config["suites"][0])
        self.assertEqual(len(cases), 3)
        for source in (haskell_runner("Pilot", cases), lean_runner("Pilot", cases)):
            self.assertIn("insert 0 []", source)
            self.assertIn("insert (-1) [(-1), 0]", source)
            self.assertIn("[(-9223372036854775808), 9223372036854775807]", source)

    def test_list_validation_rejects_wrong_shape_and_out_of_range_values(self):
        for vectors in ([[0, 1]], [[0, [True]]], [[0, [1 << 63]]]):
            with self.subTest(vectors=vectors), self.assertRaises(ValueError):
                self.load(self.config(vectors))

    def test_ordlist_function_bodies_match_pinned_upstream_slice(self):
        source = (Path(__file__).resolve().parents[1] / "tests/pilot/data-ordlist/OrderedPilot.hs").read_text()
        expected = {
            "isSortedBy": "7e544c6d064e9a3e308dad312a8cf5a26dc7c3f980c897c3158cc2bbce722425",
            "memberBy": "2146bd9e474c2ee48dc451e5060cfe12a9ff2c13e16a806e7b4819f349d0a597",
            "insertSetBy": "f0af7e5cf4bebc339992492e5e876e5039eb2b84375ad9ac52073b3c846ab1c7",
        }
        for name, digest in expected.items():
            with self.subTest(function=name):
                match = re.search(r"^" + name + r" ::.*?(?=\n\n)", source,
                                  re.MULTILINE | re.DOTALL)
                self.assertIsNotNone(match)
                self.assertEqual(hashlib.sha256(match.group(0).encode()).hexdigest(), digest)


if __name__ == "__main__":
    unittest.main()
