"""The package proof gate must reject an unreviewed axiom or missing Blaster use."""

import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from pipeline import PipelineError
from plutus_package_core import proof_axioms


NAMES = ("package_rev_append_spec", "package_reverse_model",
         "package_reverse_involutive", "package_reverse_length",
         "package_rev_append_length")


def audit_output(length_axioms):
    entries = [{"name": "PlutusTx.List." + name,
                "axioms": ["propext"] if name != "package_rev_append_length"
                else length_axioms} for name in NAMES]
    return "GHCCORE_AUDIT:" + json.dumps(entries) + "\n"


class PackageProofAuditTests(unittest.TestCase):
    def test_blaster_length_law_is_accepted(self):
        axioms = proof_axioms(audit_output(["propext", "Blaster.Tactic.blasterProven"]))
        self.assertEqual(axioms["package_rev_append_length"],
                         ["Blaster.Tactic.blasterProven", "propext"])

    def test_missing_or_extra_axiom_fails(self):
        for axioms in (["propext"],
                       ["propext", "Blaster.Tactic.blasterProven", "sorryAx"]):
            with self.subTest(axioms=axioms), self.assertRaises(PipelineError):
                proof_axioms(audit_output(axioms))

    def test_missing_theorem_fails(self):
        output = audit_output(["propext", "Blaster.Tactic.blasterProven"])
        output = output.replace('"PlutusTx.List.package_reverse_model"',
                                '"PlutusTx.List.unexpected_model"')
        with self.assertRaises(PipelineError):
            proof_axioms(output)
