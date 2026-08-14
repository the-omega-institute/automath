import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).with_name("verify_A9_r1.py")


def load_verifier():
    spec = importlib.util.spec_from_file_location("verify_A9_r1", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class OracleA9R1VerificationTests(unittest.TestCase):
    def test_real_cechization_identities(self):
        verifier = load_verifier()
        result = verifier.check_real_cechization_identities()
        self.assertGreater(result["group_cocycle_cases"], 0)
        self.assertGreater(result["tau_rewrite_cases"], 0)
        self.assertGreater(result["cech_cocycle_cases"], 0)

    def test_finite_quotient_and_exact_sequence_claims(self):
        verifier = load_verifier()
        result = verifier.check_finite_quotient_claims(max_modulus=36)
        self.assertGreater(result["factorization_cases"], 0)
        self.assertGreater(result["exact_sequence_cases"], 0)

    def test_generator_bound_classification(self):
        verifier = load_verifier()
        result = verifier.check_generator_bound_classification()
        self.assertGreater(result["groups"], 0)
        self.assertGreater(result["classification_cases"], 0)

    def test_pullback_is_not_image_equality(self):
        verifier = load_verifier()
        self.assertEqual(
            verifier.pullback_strict_inclusion_example(),
            {
                "ambient_image": frozenset({0, 1}),
                "pullback_image": frozenset({0}),
                "ambient_quotient_order": 1,
                "pullback_quotient_order": 2,
            },
        )

    def test_action_lift_need_not_satisfy_peiffer_identity(self):
        verifier = load_verifier()
        result = verifier.action_lift_peiffer_counterexample()
        self.assertTrue(result["covers_conjugation"])
        self.assertTrue(result["fixes_central_kernel"])
        self.assertFalse(result["peiffer_identity"])


if __name__ == "__main__":
    unittest.main()
