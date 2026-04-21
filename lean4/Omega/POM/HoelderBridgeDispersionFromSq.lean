import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Omega.POM.FiberDispersionIndex

namespace Omega.POM

open scoped BigOperators

namespace FiberDispersionIndexData

/-- The quadratic collision moment `S₂ = ∑ d_x²`. -/
noncomputable def sqMoment (D : FiberDispersionIndexData) : ℝ :=
  ∑ i, D.fiberSize i ^ (2 : ℕ)

lemma sqMoment_controls_totalMass (D : FiberDispersionIndexData) :
    D.totalMass ^ (2 : ℕ) ≤ (D.m : ℝ) * D.sqMoment := by
  simpa [FiberDispersionIndexData.totalMass, sqMoment] using
    (pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin D.m)))
      (f := D.fiberSize)
      (fun i _ => le_of_lt (D.fiberSize_pos i))
      1)

end FiberDispersionIndexData

open FiberDispersionIndexData

/-- Paper label: `prop:pom-hoelder-bridge-dispersion-from-Sq`. The square moment already controls
the total mass by Cauchy-Schwarz/Jensen, and the existing quadratic dispersion index remains
bounded below by `1`. -/
theorem paper_pom_hoelder_bridge_dispersion_from_sq (D : FiberDispersionIndexData) :
    D.totalMass ^ (2 : ℕ) ≤ (D.m : ℝ) * D.sqMoment ∧ 1 ≤ D.dispersionIndex := by
  exact ⟨D.sqMoment_controls_totalMass, D.dispersionIndex_ge_one⟩

end Omega.POM
