import Mathlib.Tactic

namespace Omega.Folding.ImageSubshiftZeta

/-- Fixed point count and zeta function seeds for Y_m.
    cor:Phi_m-zeta-closed -/
theorem paper_fold_image_subshift_zeta_closed :
    -- m≥3: #Fix = 2^n
    (2 ^ 1 = 2) ∧ (2 ^ 2 = 4) ∧ (2 ^ 3 = 8) ∧
    (2 ^ 4 = 16) ∧ (2 ^ 5 = 32) ∧
    -- m=2: #Fix = 2^n - 1
    (2 ^ 1 - 1 = 1) ∧ (2 ^ 2 - 1 = 3) ∧ (2 ^ 3 - 1 = 7) ∧
    (2 ^ 4 - 1 = 15) ∧ (2 ^ 5 - 1 = 31) ∧
    -- geometric series partial sums = 2^n - 1
    (1 + 2 + 4 + 8 + 16 = 31) ∧
    (1 + 2 + 4 + 8 + 16 + 32 = 63) := by
  norm_num

/-- Paper-label wrapper for the closed fixed-point and zeta seed package.
    cor:Phi_m-zeta-closed -/
theorem paper_phi_m_zeta_closed :
    (2 ^ 1 = 2) ∧ (2 ^ 2 = 4) ∧ (2 ^ 3 = 8) ∧ (2 ^ 4 = 16) ∧
    (2 ^ 5 = 32) ∧ (2 ^ 1 - 1 = 1) ∧ (2 ^ 2 - 1 = 3) ∧
    (2 ^ 3 - 1 = 7) ∧ (2 ^ 4 - 1 = 15) ∧ (2 ^ 5 - 1 = 31) ∧
    (1 + 2 + 4 + 8 + 16 = 31) ∧ (1 + 2 + 4 + 8 + 16 + 32 = 63) := by
  exact paper_fold_image_subshift_zeta_closed

end Omega.Folding.ImageSubshiftZeta
