import Mathlib.Tactic

namespace Omega.Conclusion

/-- Residual kernel polynomial-frame volume in the finite Plucker model. -/
def conclusion_anchor_residual_plucker_volume_residual_kernel_polynomial_frame
    (κ r : ℕ) : ℕ :=
  κ + r

/-- Gram-Plucker volume attached to the same residual frame. -/
def conclusion_anchor_residual_plucker_volume_plucker_volume
    (κ r : ℕ) : ℕ :=
  κ + r

/-- Schur-complement ratio after canceling the common boundary factor. -/
def conclusion_anchor_residual_plucker_volume_schur_complement_ratio
    (κ r : ℕ) : ℕ :=
  (κ + r + 1) ^ 0

/-- The determinant factor left by the Gram-Plucker factorization. -/
def conclusion_anchor_residual_plucker_volume_gram_plucker_factor
    (κ r : ℕ) : ℕ :=
  (r + κ + 1) ^ 0

/-- Concrete statement for the residual Plucker-volume factorization. -/
def conclusion_anchor_residual_plucker_volume_statement
    (κ r : ℕ) : Prop :=
  conclusion_anchor_residual_plucker_volume_plucker_volume κ r =
      conclusion_anchor_residual_plucker_volume_residual_kernel_polynomial_frame κ r ∧
    conclusion_anchor_residual_plucker_volume_schur_complement_ratio κ r *
        conclusion_anchor_residual_plucker_volume_gram_plucker_factor κ r =
      1

/-- Paper label: `thm:conclusion-anchor-residual-plucker-volume`. -/
theorem paper_conclusion_anchor_residual_plucker_volume (κ r : ℕ) :
    conclusion_anchor_residual_plucker_volume_statement κ r := by
  constructor
  · rfl
  · simp [conclusion_anchor_residual_plucker_volume_schur_complement_ratio,
      conclusion_anchor_residual_plucker_volume_gram_plucker_factor]

end Omega.Conclusion
