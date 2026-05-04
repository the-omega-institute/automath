import Mathlib.Tactic
import Omega.Kronecker.W1DenominatorClosedForm

namespace Omega.Kronecker

/-- Paper label: `thm:xi-kronecker-w1-rational-threshold-c1-nonc2-cusp`. -/
theorem paper_xi_kronecker_w1_rational_threshold_c1_nonc2_cusp (q : Nat) (hq : 2 ≤ q) :
    (∀ δ : ℚ,
      kroneckerBadSideW1 q δ =
        (1 : ℚ) / (2 * q) - ((q - 1 : Nat) : ℚ) / 2 * δ) ∧
    (∀ δ : ℚ,
      kroneckerGoodSideW1 q δ =
        (1 : ℚ) / (2 * q) - ((q - 1 : Nat) : ℚ) / 2 * δ +
          ((q * (q - 1) * (2 * q - 1) : Nat) : ℚ) / 6 * δ ^ 2) ∧
    0 < (((q * (q - 1) * (2 * q - 1) : Nat) : ℚ) / 3) := by
  have hq_pos : 0 < q := by omega
  have hqm1_pos : 0 < q - 1 := by omega
  have h2qm1_pos : 0 < 2 * q - 1 := by omega
  have hprod_pos : 0 < q * (q - 1) * (2 * q - 1) :=
    Nat.mul_pos (Nat.mul_pos hq_pos hqm1_pos) h2qm1_pos
  have hprod_rat_pos : (0 : ℚ) < ((q * (q - 1) * (2 * q - 1) : Nat) : ℚ) := by
    exact_mod_cast hprod_pos
  refine ⟨?_, ?_, ?_⟩
  · intro δ
    rfl
  · intro δ
    rfl
  · exact div_pos hprod_rat_pos (by norm_num : (0 : ℚ) < 3)

end Omega.Kronecker
