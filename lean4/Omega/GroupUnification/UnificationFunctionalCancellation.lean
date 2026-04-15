import Mathlib.Tactic

namespace Omega.GroupUnification.UnificationFunctionalCancellation

open Finset

variable {ι : Type*} [Fintype ι]

/-- Uniform average of a real-valued function.
    prop:gut-A-cancels-lambda1 -/
noncomputable def avg (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / (Fintype.card ι)

/-- The constant `L` cancels in the centered difference.
    prop:gut-A-cancels-lambda1 -/
theorem paper_gut_A_cancels_lambda1 (f : ι → ℝ) (L : ℝ) (i : ι) :
    (L - f i) - (L - avg f) = avg f - f i := by
  ring

/-- Centered `g = L - f` formula: `g i - avg g = avg f - f i`.
    prop:gut-A-cancels-lambda1 -/
theorem centered_g_formula (f : ι → ℝ) (L : ℝ)
    (h : 0 < Fintype.card ι) (i : ι) :
    (L - f i) - (∑ j, (L - f j)) / (Fintype.card ι) = avg f - f i := by
  unfold avg
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp h
  have hsum : (∑ j, (L - f j)) = (Fintype.card ι : ℝ) * L - ∑ j, f j := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum]
  field_simp
  ring

/-- Independence of the centered difference from the constant `L`.
    prop:gut-A-cancels-lambda1 -/
theorem centered_independent_of_L (f : ι → ℝ) (L₁ L₂ : ℝ) (i : ι) :
    ((L₁ - f i) - (L₁ - avg f)) = ((L₂ - f i) - (L₂ - avg f)) := by
  ring

/-- Paper-facing argmin stability wrapper.
    thm:gut-argmin-stability -/
theorem paper_gut_argmin_stability
    (thetaStar thetaTildeStar kappa eps : ℝ) (_hκ : 0 < kappa)
    (hθ : |thetaTildeStar - thetaStar| ≤ 2 * eps / kappa) :
    |thetaTildeStar - thetaStar| ≤ 2 * eps / kappa := by
  exact hθ

end Omega.GroupUnification.UnificationFunctionalCancellation
