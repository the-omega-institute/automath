import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-defect-entropy-schur-concavity`. -/
theorem paper_xi_defect_entropy_schur_concavity (a b eps : ℝ) (ha : 0 < a)
    (hb : 0 < b) (heps : 0 < eps) (hab : a ≤ b) (hmove : eps ≤ (b - a) / 2) :
    a / (1 + a) + b / (1 + b) <
      (a + eps) / (1 + a + eps) + (b - eps) / (1 + b - eps) := by
  have _ : a ≤ b := hab
  have ha_den : 0 < 1 + a := by nlinarith
  have hae_den : 0 < 1 + a + eps := by nlinarith
  have hbe_den : 0 < 1 + b - eps := by nlinarith
  have hb_den : 0 < 1 + b := by nlinarith
  have hbalanced : a + eps ≤ b - eps := by nlinarith [hab]
  have hleft_lt : 1 + a < 1 + b - eps := by nlinarith
  have hright_le : 1 + a + eps ≤ 1 + b := by nlinarith
  have hprod_lt : (1 + a) * (1 + a + eps) < (1 + b - eps) * (1 + b) := by
    calc
      (1 + a) * (1 + a + eps) < (1 + b - eps) * (1 + a + eps) := by
        exact mul_lt_mul_of_pos_right hleft_lt hae_den
      _ ≤ (1 + b - eps) * (1 + b) := by
        exact mul_le_mul_of_nonneg_left hright_le (le_of_lt hbe_den)
  field_simp [ha_den.ne', hb_den.ne', hae_den.ne', hbe_den.ne']
  nlinarith

end Omega.Zeta
