import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.CircleDimension

/-- The Stieltjes transform of the one-atom model used to package the Poisson variance lower
bound. -/
noncomputable def poissonVarianceStieltjes (s : ℝ) : ℝ :=
  1 / (s + 1)

/-- The monotone lower bound extracted from the Stieltjes transform along the ray `s = t^2`. -/
noncomputable def poissonVarianceLowerBound (t : ℝ) : ℝ :=
  1 - poissonVarianceStieltjes (t ^ 2)

private lemma poissonVarianceLowerBound_eq (t : ℝ) :
    poissonVarianceLowerBound t = t ^ 2 / (t ^ 2 + 1) := by
  unfold poissonVarianceLowerBound poissonVarianceStieltjes
  have hden : (t ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

private lemma poissonVarianceLowerBound_monotone :
    MonotoneOn poissonVarianceLowerBound (Set.Ici 0) := by
  intro a ha b hb hab
  rw [poissonVarianceLowerBound_eq, poissonVarianceLowerBound_eq]
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
  have ha' : 0 < a ^ 2 + 1 := by positivity
  have hb' : 0 < b ^ 2 + 1 := by positivity
  have hdiff :
      b ^ 2 / (b ^ 2 + 1) - a ^ 2 / (a ^ 2 + 1) =
        (b ^ 2 - a ^ 2) / ((a ^ 2 + 1) * (b ^ 2 + 1)) := by
    field_simp [ha'.ne', hb'.ne']
    ring
  have hnonneg :
      0 ≤ (b ^ 2 - a ^ 2) / ((a ^ 2 + 1) * (b ^ 2 + 1)) := by
    have hnum : 0 ≤ b ^ 2 - a ^ 2 := by nlinarith
    have hden : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) := mul_pos ha' hb'
    exact div_nonneg hnum hden.le
  nlinarith [hnonneg, hdiff]

/-- Rewriting the centered Poisson variance certificate through the Stieltjes transform
`m(s) = 1 / (s + 1)` with `s = t^2` yields the explicit lower bound `t^2 / (t^2 + 1)`. This
bound is monotone on `[0, ∞)` and converges to `1` in the far field.
    prop:cdim-poisson-variance-monotone-lower-bound -/
theorem paper_cdim_poisson_variance_monotone_lower_bound :
    MonotoneOn poissonVarianceLowerBound (Set.Ici 0) ∧
      Tendsto poissonVarianceLowerBound atTop (𝓝 1) ∧
      ∀ t : ℝ, 0 ≤ t → poissonVarianceLowerBound t = t ^ 2 / (t ^ 2 + 1) := by
  refine ⟨poissonVarianceLowerBound_monotone, ?_, ?_⟩
  · have hsq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := by
      exact tendsto_pow_atTop (by omega : (2 : ℕ) ≠ 0)
    have hshift : Tendsto (fun t : ℝ => t ^ 2 + 1) atTop atTop := by
      exact tendsto_atTop_add_const_right _ _ hsq
    have hinv : Tendsto (fun t : ℝ => (t ^ 2 + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hshift
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hmain : Tendsto (fun t : ℝ => 1 - (t ^ 2 + 1)⁻¹) atTop (𝓝 1) := by
      simpa using hconst.sub hinv
    convert hmain using 1
    funext t
    simp [poissonVarianceLowerBound, poissonVarianceStieltjes, one_div]
  · intro t _ht
    exact poissonVarianceLowerBound_eq t

end Omega.CircleDimension
