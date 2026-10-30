"""Structural checks for the published conservative support inventory."""

import json
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "docs" / "support-table.json"


class SupportTableTest(unittest.TestCase):
    def test_entries_are_unique_complete_and_evidenced(self):
        table = json.loads(TABLE.read_text(encoding="utf-8"))
        self.assertEqual(table["schemaVersion"], 1)
        self.assertEqual(table["policy"], "conservative")
        self.assertEqual(table["claim"], "lean-model")
        self.assertIs(table["translationCertified"], False)

        statuses = set(table["entryStatus"])
        self.assertEqual(statuses, {"guarded", "conditional", "refused"})
        entries = table["entries"]
        self.assertTrue(entries)
        keys = [entry["key"] for entry in entries]
        self.assertEqual(len(keys), len(set(keys)), "duplicate support keys")

        required = {"key", "status", "sourceBehavior", "leanImage", "domain", "refusal", "evidence"}
        for entry in entries:
            with self.subTest(key=entry["key"]):
                self.assertEqual(set(entry), required)
                self.assertIn(entry["status"], statuses)
                for field in required - {"evidence"}:
                    self.assertIsInstance(entry[field], str)
                    self.assertTrue(entry[field].strip())
                self.assertTrue(entry["evidence"])
                for source in entry["evidence"]:
                    self.assertFalse(Path(source).is_absolute())
                    self.assertTrue((ROOT / source).is_file(), source)


if __name__ == "__main__":
    unittest.main()
