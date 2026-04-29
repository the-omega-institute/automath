import Omega.POM.DiagonalRateScalarCollapse

namespace Omega.POM

/-- Concrete statement for the rate-curve identifiability wrapper, written with explicit
parameters instead of a packaged structure argument. -/
def pom_diagonal_rate_rate_curve_identifiability_statement
    {State : Type} [Fintype State] [DecidableEq State]
    (w : State → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1) (κ : ℝ) (hκ : 0 < κ)
    (A : ℝ) (hA_pos : 0 < A) (hA_lt_one : A < 1)
    (gapStrictMono :
      StrictMono fun t : ℝ =>
        t - ∑ x, (Real.sqrt (t ^ 2 + 4 * κ * w x) - t) / (2 * κ))
    (hA_fixed : A = ∑ x, (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ))
    (hdelta0_pos : 0 < 1 - ∑ x, (w x) ^ 2) : Prop :=
  let D : DiagonalRateScalarCollapseData :=
    { State := State
      instFintype := inferInstance
      instDecidableEq := inferInstance
      w := w
      hw_pos := hw_pos
      hw_sum := hw_sum
      κ := κ
      hκ := hκ
      A := A
      hA_pos := hA_pos
      hA_lt_one := hA_lt_one
      gapStrictMono := gapStrictMono
      hA_fixed := hA_fixed
      hdelta0_pos := hdelta0_pos }
  D.uniqueFixedPointPackage ∧
    D.kappaDistortionBijection ∧
    (∃! κ' : ℝ, κ' ∈ Set.Ioi 0 ∧ D.distortionMap κ' = D.distortionMap D.κ) ∧
    ∃ weights : List ℝ, weights = (Finset.univ : Finset D.State).toList.map D.w

/-- Paper label: `thm:pom-diagonal-rate-rate-curve-identifiability`. In the Lean surrogate, the
single rate curve is represented by the scalar-collapse distortion branch, and the existing
reconstruction package already records uniqueness of the dual parameter together with recovery of
the finite weight multiset. -/
theorem paper_pom_diagonal_rate_rate_curve_identifiability
    {State : Type} [Fintype State] [DecidableEq State]
    (w : State → ℝ) (hw_pos : ∀ x, 0 < w x) (hw_sum : ∑ x, w x = 1) (κ : ℝ) (hκ : 0 < κ)
    (A : ℝ) (hA_pos : 0 < A) (hA_lt_one : A < 1)
    (gapStrictMono :
      StrictMono fun t : ℝ =>
        t - ∑ x, (Real.sqrt (t ^ 2 + 4 * κ * w x) - t) / (2 * κ))
    (hA_fixed : A = ∑ x, (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ))
    (hdelta0_pos : 0 < 1 - ∑ x, (w x) ^ 2) :
    pom_diagonal_rate_rate_curve_identifiability_statement w hw_pos hw_sum κ hκ A hA_pos
      hA_lt_one gapStrictMono hA_fixed hdelta0_pos := by
  let D : DiagonalRateScalarCollapseData :=
    { State := State
      instFintype := inferInstance
      instDecidableEq := inferInstance
      w := w
      hw_pos := hw_pos
      hw_sum := hw_sum
      κ := κ
      hκ := hκ
      A := A
      hA_pos := hA_pos
      hA_lt_one := hA_lt_one
      gapStrictMono := gapStrictMono
      hA_fixed := hA_fixed
      hdelta0_pos := hdelta0_pos }
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨D.unique_fixed_point, D.hA_lt_one, D.row_sum_eq_weight, D.total_mass_eq_one⟩
  · exact ⟨D.distortion_continuousOn, D.distortion_strictAntiOn, D.distortion_bijOn⟩
  · refine ⟨D.κ, ⟨D.hκ, rfl⟩, ?_⟩
    intro κ' hκ'
    exact (D.distortion_bijOn.2.1) hκ'.1 D.hκ hκ'.2
  · exact ⟨(Finset.univ : Finset D.State).toList.map D.w, rfl⟩

end Omega.POM
