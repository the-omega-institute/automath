import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the conjugacy-class primitive decomposition.
    thm:class-primitive-decomposition -/
theorem paper_etds_class_primitive_decomposition
    {Irr : Type}
    [Fintype Irr]
    (classWeight primitiveSeries primitiveCoefficients : ℂ)
    (seriesCoeff coeffWeight : Irr → ℂ)
    (hSeries :
      primitiveSeries =
        classWeight * ∑ ρ, coeffWeight ρ * seriesCoeff ρ)
    (hCoefficients :
      primitiveCoefficients =
        classWeight * ∑ ρ, coeffWeight ρ * seriesCoeff ρ) :
    primitiveSeries =
        classWeight * ∑ ρ, coeffWeight ρ * seriesCoeff ρ ∧
      primitiveCoefficients =
        classWeight * ∑ ρ, coeffWeight ρ * seriesCoeff ρ := by
  exact ⟨hSeries, hCoefficients⟩

end Omega.Zeta
