import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace Omega.Discussion

open intervalIntegral

/-- Concrete interval-integral corollary of the logistic variance-gap differential identity. -/
def discussion_variance_gap_integral_package
    (κ s₀ s₁ : ℝ) (S V : ℝ → ℝ) : Prop :=
  ∀ _hderiv : deriv S = fun s => S s * (1 - S s / κ) - κ * V s,
    (∀ s ∈ Set.uIcc s₀ s₁, DifferentiableAt ℝ S s) →
    ContinuousOn (fun s => S s * (1 - S s / κ) - κ * V s) (Set.uIcc s₀ s₁) →
    IntervalIntegrable V MeasureTheory.volume s₀ s₁ →
      ∫ s in s₀..s₁, κ * V s =
        (∫ s in s₀..s₁, S s * (1 - S s / κ)) - (S s₁ - S s₀)

/-- Paper label: `con:discussion-variance-gap-integral`. Integrating the differential identity
`S' = S (1 - S / κ) - κ V` over `[s₀, s₁]` and rearranging isolates the accumulated variance-gap
term on the left-hand side. -/
theorem paper_discussion_variance_gap_integral
    (κ s₀ s₁ : ℝ) (S V : ℝ → ℝ) :
    discussion_variance_gap_integral_package κ s₀ s₁ S V := by
  dsimp [discussion_variance_gap_integral_package]
  intro hderiv hdiff hcont hVint
  have hScont : ContinuousOn S (Set.uIcc s₀ s₁) := by
    intro s hs
    exact (hdiff s hs).continuousAt.continuousWithinAt
  have hlogisticCont : ContinuousOn (fun s => S s * (1 - S s / κ)) (Set.uIcc s₀ s₁) := by
    refine hScont.mul ?_
    exact continuousOn_const.sub (hScont.div_const κ)
  have hmain :
      ∫ s in s₀..s₁, (fun s => S s * (1 - S s / κ) - κ * V s) s = S s₁ - S s₀ := by
    simpa using intervalIntegral.integral_deriv_eq_sub' S hderiv hdiff hcont
  have hsub :
      ∫ s in s₀..s₁, (fun s => S s * (1 - S s / κ) - κ * V s) s =
        (∫ s in s₀..s₁, S s * (1 - S s / κ)) - κ * ∫ s in s₀..s₁, V s := by
    rw [intervalIntegral.integral_sub hlogisticCont.intervalIntegrable (hVint.const_mul κ)]
    rw [intervalIntegral.integral_const_mul]
  rw [hsub] at hmain
  have hkv :
      ∫ s in s₀..s₁, κ * V s = κ * ∫ s in s₀..s₁, V s := by
    rw [intervalIntegral.integral_const_mul]
  set A : ℝ := ∫ s in s₀..s₁, S s * (1 - S s / κ) with hA
  set B : ℝ := κ * ∫ s in s₀..s₁, V s with hB
  set C : ℝ := S s₁ - S s₀ with hC
  have hmain' : A - B = C := by
    simpa [hA, hB, hC] using hmain
  have hresult :
      B = A - C := by
    linarith
  calc
    ∫ s in s₀..s₁, κ * V s = B := by
      rw [hB]
      exact hkv
    _ = A - C := hresult
    _ = (∫ s in s₀..s₁, S s * (1 - S s / κ)) - (S s₁ - S s₀) := by
      rw [hA, hC]

end Omega.Discussion
