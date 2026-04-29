import Omega.POM.DiagonalRateScalarCollapse

namespace Omega.POM

open DiagonalRateScalarCollapseData

/-- Concrete reconstruction package extracted from the scalar-collapse model: the distortion value
at `D.κ` determines `κ` uniquely, and the recovered weight multiset is recorded by the finite list
obtained from enumerating the state space. -/
def pom_diagonal_rate_reconstruct_w_from_rate_curve_statement
    (D : DiagonalRateScalarCollapseData) : Prop :=
  D.uniqueFixedPointPackage ∧
    D.kappaDistortionBijection ∧
    (∃! κ' : ℝ, κ' ∈ Set.Ioi 0 ∧ D.distortionMap κ' = D.distortionMap D.κ) ∧
    ∃ weights : List ℝ, weights = (Finset.univ : Finset D.State).toList.map D.w

/-- Paper label: `prop:pom-diagonal-rate-reconstruct-w-from-rate-curve`. In the Lean model, the
scalar-collapse package already gives a bijective distortion curve, so the distortion value at
`D.κ` recovers `κ` uniquely; the corresponding weight output is the enumerated list of weights. -/
theorem paper_pom_diagonal_rate_reconstruct_w_from_rate_curve (D : DiagonalRateScalarCollapseData) :
    pom_diagonal_rate_reconstruct_w_from_rate_curve_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨D.unique_fixed_point, D.hA_lt_one, D.row_sum_eq_weight, D.total_mass_eq_one⟩
  · exact ⟨D.distortion_continuousOn, D.distortion_strictAntiOn, D.distortion_bijOn⟩
  · refine ⟨D.κ, ⟨D.hκ, rfl⟩, ?_⟩
    intro κ' hκ'
    exact (D.distortion_bijOn.2.1) hκ'.1 D.hκ hκ'.2
  · exact ⟨(Finset.univ : Finset D.State).toList.map D.w, rfl⟩

end Omega.POM
