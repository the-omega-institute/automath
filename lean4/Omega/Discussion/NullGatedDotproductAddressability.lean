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

/-- The exponential spherical-cap tail used for the distractor budget. -/
noncomputable def sphericalCapSubgaussianBound (d : ℕ) (τ : ℝ) : ℝ :=
  Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))

/-- If the first-coordinate tail is bounded by the standard spherical-cap estimate and rotational
symmetry identifies the tail for a fixed unit query with that first-coordinate tail, then the same
subgaussian bound holds for the query direction.
    `lem:discussion-spherical-cap-subgaussian` -/
theorem paper_discussion_spherical_cap_subgaussian
    (d : ℕ) (τ firstCoordTail queryTail : ℝ)
    (hcoord : firstCoordTail ≤ sphericalCapSubgaussianBound d τ)
    (hrotation : queryTail = firstCoordTail) :
    queryTail ≤ sphericalCapSubgaussianBound d τ := by
  simpa [sphericalCapSubgaussianBound, hrotation] using hcoord

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

/-- The null-hit contribution is at most `δ/2` once the per-query null budget is at most
`δ / (2N)`. -/
lemma nullHitBudget_le_half_delta
    (N : ℕ) {εnull δ : ℝ} (hN : 1 ≤ N)
    (hε : εnull ≤ δ / (2 * (N : ℝ))) :
    nullHitBudget N εnull ≤ δ / 2 := by
  unfold nullHitBudget
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hε hN0
  have hN_ne : (N : ℝ) ≠ 0 := by positivity
  calc
    (N : ℝ) * εnull ≤ (N : ℝ) * (δ / (2 * (N : ℝ))) := hmul
    _ = δ / 2 := by
      field_simp [hN_ne]

/-- The distractor contribution is at most `δ/2` once the logarithmic lower bound on `d` forces
the exponential tail below `δ / (2N²)`. -/
lemma wrongHitBudget_le_half_delta_of_log_bound
    (d N : ℕ) {τ δ : ℝ} (hN : 1 ≤ N) (hδ : 0 < δ)
    (hlog : Real.log (2 * (N : ℝ) ^ 2 / δ) ≤ (((d : ℝ) - 1) * τ ^ 2 / 2)) :
    wrongHitBudget d N τ ≤ δ / 2 := by
  unfold wrongHitBudget
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hNm1_le : (N - 1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N 1
  have hquad :
      (N : ℝ) * (N - 1 : ℝ) ≤ (N : ℝ) ^ 2 := by
    nlinarith
  have hlogArg_pos : 0 < 2 * (N : ℝ) ^ 2 / δ := by
    positivity
  have hexp_le :
      Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2)) ≤ δ / (2 * (N : ℝ) ^ 2) := by
    have hneg :
        -(((d : ℝ) - 1) * τ ^ 2 / 2) ≤ -Real.log (2 * (N : ℝ) ^ 2 / δ) := by
      linarith
    calc
      Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))
          ≤ Real.exp (-Real.log (2 * (N : ℝ) ^ 2 / δ)) := by
            exact Real.exp_le_exp.mpr hneg
      _ = δ / (2 * (N : ℝ) ^ 2) := by
            rw [Real.exp_neg, Real.exp_log hlogArg_pos]
            field_simp [show (2 : ℝ) * (N : ℝ) ^ 2 ≠ 0 by positivity]
  have hsq_pos : 0 < (N : ℝ) ^ 2 := by
    have hN_pos : 0 < (N : ℝ) := by positivity
    positivity
  have hmain :
      (N : ℝ) * (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))
        ≤ (N : ℝ) ^ 2 * (δ / (2 * (N : ℝ) ^ 2)) := by
    have hexp_nonneg :
        0 ≤ Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2)) := by positivity
    have hstep1 :
        (N : ℝ) * (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))
          ≤ (N : ℝ) ^ 2 * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2)) := by
      gcongr
    have hstep2 :
        (N : ℝ) ^ 2 * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))
          ≤ (N : ℝ) ^ 2 * (δ / (2 * (N : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hexp_le (sq_nonneg (N : ℝ))
    exact le_trans hstep1 hstep2
  have hN_sq_ne : (N : ℝ) ^ 2 ≠ 0 := by positivity
  calc
    (N : ℝ) * (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2))
      ≤ (N : ℝ) ^ 2 * (δ / (2 * (N : ℝ) ^ 2)) := hmain
    _ = δ / 2 := by
      field_simp [hN_sq_ne]

/-- If the null term and the distractor term are each forced below `δ/2`, then the existing
null-gated failure-budget theorem yields the paper's fixed-confidence dimension threshold. -/
theorem paper_discussion_null_gated_dotproduct_min_d
    (d N : ℕ) (τ εnull δ : ℝ)
    (failure nullHit wrongHit : Fin N → ℝ)
    (hfailure : ∀ i, failure i ≤ nullHit i + wrongHit i)
    (hnull : ∀ i, nullHit i ≤ εnull)
    (hwrong : ∀ i,
      wrongHit i ≤ (N - 1 : ℝ) * Real.exp (-(((d : ℝ) - 1) * τ ^ 2 / 2)))
    (hN : 1 ≤ N) (hδ : 0 < δ)
    (hε : εnull ≤ δ / (2 * (N : ℝ)))
    (hlog : Real.log (2 * (N : ℝ) ^ 2 / δ) ≤ (((d : ℝ) - 1) * τ ^ 2 / 2)) :
    (∑ i, failure i) ≤ δ := by
  have hBudget :
      (∑ i, failure i) ≤ nullGatedFailureBudget d N τ εnull :=
    paper_discussion_null_gated_dotproduct_addressability d N τ εnull failure nullHit wrongHit
      hfailure hnull hwrong
  have hNullHalf : nullHitBudget N εnull ≤ δ / 2 :=
    nullHitBudget_le_half_delta N hN hε
  have hWrongHalf : wrongHitBudget d N τ ≤ δ / 2 :=
    wrongHitBudget_le_half_delta_of_log_bound d N hN hδ hlog
  calc
    (∑ i, failure i) ≤ nullGatedFailureBudget d N τ εnull := hBudget
    _ = nullHitBudget N εnull + wrongHitBudget d N τ := by
          simp [nullGatedFailureBudget]
    _ ≤ δ / 2 + δ / 2 := add_le_add hNullHalf hWrongHalf
    _ = δ := by ring

end Omega.Discussion
