import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Omega.SyncKernelRealInput.FiniteRh40
import Omega.SyncKernelWeighted.PrimitiveOddEvenSqrtCancellation

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Concrete data for the finite-RH explicit-formula package: a verified spectrum audit together
with the truncation level of the finite sequence argument. -/
structure finite_rh_explicit_formula_data where
  base : finite_rh_40_data
  n : ℕ

/-- The explicit-formula package reuses the finite-RH spectrum audit, the positive Perron main
coefficient, and the constructive odd/even primitive-count split at the audited Perron base. -/
def finite_rh_explicit_formula_statement (D : finite_rh_explicit_formula_data) : Prop :=
  finite_rh_40_statement D.base ∧
    0 < finite_rh_40_main_coeff ∧
    Omega.SyncKernelWeighted.primitiveOddEvenTrace finite_rh_40_lambda D.n =
      finite_rh_40_lambda ^ D.n + (-1 : ℝ) ^ D.n * finite_rh_40_lambda ^ (D.n / 2) ∧
    (2 ∣ D.n →
      Omega.SyncKernelWeighted.primitiveOddEvenPrimitiveCount finite_rh_40_lambda D.n =
        finite_rh_40_lambda ^ D.n / D.n -
          ((-1 : ℝ) ^ (D.n / 2) * finite_rh_40_lambda ^ (D.n / 4)) / D.n) ∧
    (¬2 ∣ D.n →
      Omega.SyncKernelWeighted.primitiveOddEvenPrimitiveCount finite_rh_40_lambda D.n =
        finite_rh_40_lambda ^ D.n / D.n - finite_rh_40_lambda ^ (D.n / 2) / D.n)

/-- Paper label: `cor:finite-rh-explicit-formula`. -/
theorem paper_finite_rh_explicit_formula (D : finite_rh_explicit_formula_data) :
    finite_rh_explicit_formula_statement D := by
  have hbase := paper_finite_rh_40 D.base
  rcases Omega.SyncKernelWeighted.paper_primitive_odd_even_sqrt_cancellation finite_rh_40_lambda D.n
      with ⟨htrace, heven, hodd⟩
  exact ⟨hbase, finite_rh_40_main_coeff_pos, htrace, heven, hodd⟩

end

end Omega.SyncKernelRealInput
