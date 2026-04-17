import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Omega.Discussion

/-- Aggregate contribution of the target-miss budget. -/
def nullHitBudget (N : ℕ) (εnull : ℝ) : ℝ := (N : ℝ) * εnull

/-- Aggregate contribution of the distractor spherical-cap tail term. -/
noncomputable def wrongHitBudget (d N : ℕ) (τ : ℝ) : ℝ :=
  (N : ℝ) * (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))

/-- Combined budget controlling the total failure probability. -/
noncomputable def nullGatedFailureBudget (d N : ℕ) (τ εnull : ℝ) : ℝ :=
  nullHitBudget N εnull + wrongHitBudget d N τ

/-- Paper-facing union-bound estimate for null-gated dot-product retrieval. The per-query failure
is bounded by a target-miss term plus a distractor term, and summing those bounds yields the
global addressability budget. -/
theorem paper_discussion_null_gated_dotproduct_addressability
    (d N : ℕ) (τ εnull : ℝ)
    (failure nullHit wrongHit : Fin N → ℝ)
    (hfailure : ∀ i, failure i ≤ nullHit i + wrongHit i)
    (hnull : ∀ i, nullHit i ≤ εnull)
    (hwrong : ∀ i,
      wrongHit i ≤ (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))) :
    (∑ i, failure i) ≤ nullGatedFailureBudget d N τ εnull := by
  have hFailureSum :
      (∑ i, failure i) ≤ ∑ i, (nullHit i + wrongHit i) := by
    exact Finset.sum_le_sum fun i _ => hfailure i
  have hNullSum :
      (∑ i, nullHit i) ≤ ∑ _i : Fin N, εnull := by
    exact Finset.sum_le_sum fun i _ => hnull i
  have hWrongSum :
      (∑ i, wrongHit i) ≤
        ∑ _i : Fin N, ((N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))) := by
    exact Finset.sum_le_sum fun i _ => hwrong i
  calc
    (∑ i, failure i) ≤ ∑ i, (nullHit i + wrongHit i) := hFailureSum
    _ = (∑ i, nullHit i) + ∑ i, wrongHit i := by rw [Finset.sum_add_distrib]
    _ ≤ (∑ _i : Fin N, εnull) +
          ∑ _i : Fin N, ((N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))) := by
          exact add_le_add hNullSum hWrongSum
    _ = (N : ℝ) * εnull + (N : ℝ) * ((N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))) := by
          simp
    _ = nullGatedFailureBudget d N τ εnull := by
          simp [nullGatedFailureBudget, nullHitBudget, wrongHitBudget]
          ring

end Omega.Discussion
