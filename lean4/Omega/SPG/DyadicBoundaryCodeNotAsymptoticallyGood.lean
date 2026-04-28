import Mathlib.Tactic
import Omega.SPG.DyadicBoundaryImageLDPC
import Omega.SPG.DyadicBoundaryImageMinDistance

namespace Omega.SPG

/-- Closed-form relative distance for the dyadic boundary image code. -/
def xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_relativeDistance
    (m n : ℕ) : ℚ :=
  2 / (((2 ^ m + 1 : ℕ) : ℚ) * ((2 ^ ((n - 1) * m) : ℕ) : ℚ))

/-- The maximum-likelihood unique-decoding radius determined by the minimum distance. -/
def xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius
    (m n : ℕ) : ℕ :=
  (dyadicBoundaryImageMinDistance m n - 1) / 2

/-- Concrete package for the dyadic boundary-image code rate, relative-distance closed form, and
fixed unique-decoding radius. -/
def xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_statement : Prop :=
  ∀ m n : ℕ,
    1 ≤ n →
      dyadicBoundaryImageBlockLength n m =
          n * (2 ^ m + 1) * 2 ^ ((n - 1) * m) ∧
        dyadicBoundaryImageMinDistance m n = 2 * n ∧
        xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_relativeDistance m n =
          2 / (((2 ^ m + 1 : ℕ) : ℚ) * ((2 ^ ((n - 1) * m) : ℕ) : ℚ)) ∧
        dyadicBoundaryImageRate n m = (2 ^ m : ℚ) / (n * (2 ^ m + 1)) ∧
        xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius m n = n - 1

lemma xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius_eq
    (m n : ℕ) (hn : 1 ≤ n) :
    xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius m n = n - 1 := by
  rw [xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius,
    paper_spg_dyadic_boundary_image_min_distance m n hn]
  omega

/-- Paper label: `cor:xi-time-part65a-dyadic-boundary-code-not-asymptotically-good`. -/
theorem paper_xi_time_part65a_dyadic_boundary_code_not_asymptotically_good :
    xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_statement := by
  intro m n hn
  refine ⟨rfl, paper_spg_dyadic_boundary_image_min_distance m n hn, rfl, rfl, ?_⟩
  exact xi_time_part65a_dyadic_boundary_code_not_asymptotically_good_uniqueRadius_eq m n hn

end Omega.SPG
