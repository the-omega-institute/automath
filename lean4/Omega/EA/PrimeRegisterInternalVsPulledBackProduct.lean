import Mathlib.Data.Nat.Factorization.Basic
import Omega.EA.PrimeRegisterExternalLedgerOrbitInvariance

namespace Omega.EA

/-- The pulled-back multiplication on canonical prime registers. -/
noncomputable def odot_pr (a b : DigitCfg) : DigitCfg :=
  R_F (valPr a * valPr b)

/-- Internal multiplication of canonical registers normalizes additively, whereas the pulled-back
value multiplication is multiplicative on values and additive on the external ledger.
    prop:prime-register-internal-vs-pulled-back-product -/
theorem paper_prime_register_internal_vs_pulled_back_product (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    NF_pr (primeRegisterMul (R_F m) (R_F n)) = R_F (m + n) ∧
      odot_pr (R_F m) (R_F n) = R_F (m * n) ∧
      externalLedger (odot_pr (R_F m) (R_F n)) =
        externalLedger (R_F m) + externalLedger (R_F n) := by
  refine ⟨(paper_prime_register_multiplicative_normalization_additive_iso).2.1 m n, ?_, ?_⟩
  · simp [odot_pr, valPr_R_F]
  · simp [externalLedger, odot_pr, valPr_R_F, Nat.factorization_mul hm.ne' hn.ne']

end Omega.EA
