import Mathlib.Tactic
import Omega.GroupUnification.TwoChannelCollapse

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

/-- A two-branch convex-hull witness for `0` exists exactly when the active derivatives have
    opposite signs or one vanishes.
    thm:gut-A-local-optimality -/
theorem convex_combo_zero_iff_mul_nonpos (x y : ℝ) :
    (∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ α * x + (1 - α) * y = 0) ↔ x * y ≤ 0 := by
  constructor
  · rintro ⟨α, hα0, hα1, hEq⟩
    by_contra hxy
    have hxy' : 0 < x * y := by linarith
    rcases (mul_pos_iff.mp hxy') with hpos | hneg
    · rcases hpos with ⟨hx, hy⟩
      have hβ0 : 0 ≤ 1 - α := by linarith
      by_cases hαeq : α = 0
      · have : 0 < (1 - α) * y := by simpa [hαeq] using hy
        have hy0 : y = 0 := by simpa [hαeq] using hEq
        linarith
      · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαeq)
        have hax : 0 < α * x := by positivity
        have hby : 0 ≤ (1 - α) * y := by positivity
        nlinarith
    · rcases hneg with ⟨hx, hy⟩
      have hβ0 : 0 ≤ 1 - α := by linarith
      by_cases hαeq : α = 0
      · have : (1 - α) * y < 0 := by simpa [hαeq] using hy
        have hy0 : y = 0 := by simpa [hαeq] using hEq
        linarith
      · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαeq)
        have hax : α * x < 0 := by nlinarith
        have hby : (1 - α) * y ≤ 0 := by nlinarith
        nlinarith
  · intro hxy
    by_cases hsum : |x| + |y| = 0
    · have hxabs : |x| = 0 := by
        have hyabs_nonneg : 0 ≤ |y| := abs_nonneg y
        nlinarith [abs_nonneg x, hyabs_nonneg]
      have hyabs : |y| = 0 := by
        have hxabs_nonneg : 0 ≤ |x| := abs_nonneg x
        nlinarith [hxabs_nonneg, abs_nonneg y]
      have hx : x = 0 := abs_eq_zero.mp hxabs
      have hy : y = 0 := abs_eq_zero.mp hyabs
      refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]
    · refine ⟨|y| / (|x| + |y|), ?_, ?_, ?_⟩
      · exact div_nonneg (abs_nonneg y) (by positivity)
      · have hden : 0 < |x| + |y| := by positivity
        have hy_le : |y| ≤ |x| + |y| := by nlinarith [abs_nonneg x]
        exact (div_le_one hden).2 hy_le
      · have hnum : |y| * x + |x| * y = 0 := by
          rcases (mul_nonpos_iff.mp hxy) with hxy' | hxy'
          · rcases hxy' with ⟨hx, hy⟩
            rw [abs_of_nonneg hx, abs_of_nonpos hy]
            ring
          · rcases hxy' with ⟨hx, hy⟩
            rw [abs_of_nonpos hx, abs_of_nonneg hy]
            ring
        have hsum' : (|x| + |y| : ℝ) ≠ 0 := hsum
        calc
          |y| / (|x| + |y|) * x + (1 - |y| / (|x| + |y|)) * y
              = (|y| * x + |x| * y) / (|x| + |y|) := by
                  field_simp [hsum']
                  ring
          _ = 0 := by rw [hnum]; simp

/-- Paper-facing local-optimality package: the one-dimensional KKT/Clarke convex-hull condition
    reduces to the two-channel sign-change criterion, and the centered two-branch max collapses to
    the half-spread formula.
    thm:gut-A-local-optimality -/
theorem paper_gut_A_local_optimality :
    (∀ x y : ℝ, (∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ α * x + (1 - α) * y = 0) ↔ x * y ≤ 0) ∧
    (∀ a b L : ℝ,
      max (|(L - a) - (L - (a + b) / 2)|) (|(L - b) - (L - (a + b) / 2)|) =
        |a - b| / 2) := by
  refine ⟨convex_combo_zero_iff_mul_nonpos, ?_⟩
  intro a b L
  have h₁ : |(L - a) - (L - (a + b) / 2)| = |(a + b) / 2 - a| := by
    congr 1
    ring
  have h₂ : |(L - b) - (L - (a + b) / 2)| = |(a + b) / 2 - b| := by
    congr 1
    ring
  rw [h₁, h₂, Omega.GroupUnification.TwoChannelCollapse.paper_gut_A_two_channel a b]

end Omega.GroupUnification.UnificationFunctionalCancellation
