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

    def test_ordered_list_pairs_cover_all_short_multisets(self):
        config = self.config([])
        operation = config["suites"][0]["operations"][0]
        operation["arguments"] = ["int64-list", "int64-list"]
        operation["orderedListPairs"] = {"values": [-1, 0, 1], "maxLength": 2}
        loaded = self.load(config)
        cases = expand_cases(loaded, loaded["suites"][0])
        self.assertEqual(len(cases), 100)
        self.assertEqual(cases[0]["inputs"], [[], []])
        self.assertIn([[0, 0], [-1, 1]], [case["inputs"] for case in cases])

    def test_ordered_list_pairs_reject_invalid_domain(self):
        config = self.config([])
        operation = config["suites"][0]["operations"][0]
        operation["arguments"] = ["int64-list", "int64-list"]
        for invalid in ({"values": [0, -1], "maxLength": 2},
                        {"values": [0, 0], "maxLength": 2},
                        {"values": [0], "maxLength": 4}):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                operation["orderedListPairs"] = invalid
                self.load(config)

    def test_ordlist_function_bodies_match_pinned_upstream_slice(self):
        source = (Path(__file__).resolve().parents[1] / "tests/pilot/data-ordlist/OrderedPilot.hs").read_text()
        expected = {
            "isSortedBy": "7e544c6d064e9a3e308dad312a8cf5a26dc7c3f980c897c3158cc2bbce722425",
            "memberBy": "2146bd9e474c2ee48dc451e5060cfe12a9ff2c13e16a806e7b4819f349d0a597",
            "insertSetBy": "f0af7e5cf4bebc339992492e5e876e5039eb2b84375ad9ac52073b3c846ab1c7",
            "unionBy": "8e016266aa0657e468a0bad6d635282975e6501b0af8a95dbe5c3761c3aa6b7c",
            "mergeBy": "873f44213c77c66f825a36b028a2aa08006e83d5ae8f991a57371c6010dc9d2e",
        }
        for name, digest in expected.items():
            with self.subTest(function=name):
                match = re.search(r"^" + name + r" ::.*?(?=\n\n)", source,
                                  re.MULTILINE | re.DOTALL)
                self.assertIsNotNone(match)
                self.assertEqual(hashlib.sha256(match.group(0).encode()).hexdigest(), digest)


if __name__ == "__main__":
    unittest.main()
