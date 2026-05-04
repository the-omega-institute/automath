import Mathlib.Tactic

namespace Omega.Conclusion

/-- One diagonal factor of the long-bulk cubic determinant. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_diagonalFactor
    (t eigenvalue : ℤ) : ℤ :=
  t - eigenvalue

/-- The determinant from the three diagonal spectral factors with eigenvalues `1, 3, 5`. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_determinantCubic
    (t : ℤ) : ℤ :=
  conclusion_window6_long_bulk_unique_affine_spectral_lift_diagonalFactor t 1 *
    conclusion_window6_long_bulk_unique_affine_spectral_lift_diagonalFactor t 3 *
      conclusion_window6_long_bulk_unique_affine_spectral_lift_diagonalFactor t 5

/-- The monic affine spectral lift selected by the multiplicity alphabet. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_affineCubic
    (t : ℤ) : ℤ :=
  t ^ 3 - 9 * t ^ 2 + 23 * t - 15

/-- Evaluation of a monic cubic with unknown lower coefficients. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval
    (a b c t : ℤ) : ℤ :=
  t ^ 3 + a * t ^ 2 + b * t + c

/-- The root constraints at the three diagonal eigenvalues. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_rootConstraints
    (a b c : ℤ) : Prop :=
  conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval a b c 1 = 0 ∧
    conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval a b c 3 = 0 ∧
      conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval a b c 5 = 0

/-- Concrete statement for the unique affine spectral lift package. -/
def conclusion_window6_long_bulk_unique_affine_spectral_lift_statement : Prop :=
  (∀ t : ℤ,
    conclusion_window6_long_bulk_unique_affine_spectral_lift_determinantCubic t =
      conclusion_window6_long_bulk_unique_affine_spectral_lift_affineCubic t) ∧
    conclusion_window6_long_bulk_unique_affine_spectral_lift_rootConstraints (-9) 23 (-15) ∧
      ∀ a b c : ℤ,
        conclusion_window6_long_bulk_unique_affine_spectral_lift_rootConstraints a b c →
          a = -9 ∧ b = 23 ∧ c = -15

/-- Paper label: `thm:conclusion-window6-long-bulk-unique-affine-spectral-lift`. -/
theorem paper_conclusion_window6_long_bulk_unique_affine_spectral_lift :
    conclusion_window6_long_bulk_unique_affine_spectral_lift_statement := by
  dsimp [conclusion_window6_long_bulk_unique_affine_spectral_lift_statement]
  refine ⟨?_, ?_, ?_⟩
  · intro t
    unfold conclusion_window6_long_bulk_unique_affine_spectral_lift_determinantCubic
      conclusion_window6_long_bulk_unique_affine_spectral_lift_affineCubic
      conclusion_window6_long_bulk_unique_affine_spectral_lift_diagonalFactor
    ring
  · norm_num [conclusion_window6_long_bulk_unique_affine_spectral_lift_rootConstraints,
      conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval]
  · intro a b c hroot
    rcases hroot with ⟨h1, h3, h5⟩
    norm_num [conclusion_window6_long_bulk_unique_affine_spectral_lift_monicCubicEval] at h1 h3 h5
    constructor
    · linarith
    constructor
    · linarith
    · linarith

end Omega.Conclusion
