import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton

/-- Chapter-local interface for the residual stress-energy tensor used just before the global
    Einstein equation. Diffeomorphism invariance is the hypothesis that produces covariant
    conservation. -/
structure DerivedResidualStressEnergy where
  stressEnergy : ℕ → ℕ → ℝ
  covariantDivergence : ℕ → ℝ
  symmetric : ∀ μ ν, stressEnergy μ ν = stressEnergy ν μ
  diffeomorphismInvariant : Prop
  hasDiffeomorphismInvariant : diffeomorphismInvariant
  conserved_of_diffeomorphismInvariant :
    diffeomorphismInvariant → ∀ μ, covariantDivergence μ = 0

/-- Paper-facing wrapper: the derived residual stress-energy tensor is symmetric, comes from a
    diffeomorphism-invariant construction, and is therefore covariantly conserved.
    prop:physical-spacetime-derived-stress-energy-conservation -/
theorem paper_physical_spacetime_derived_stress_energy_conservation
    (T : DerivedResidualStressEnergy) :
    (∀ μ ν, T.stressEnergy μ ν = T.stressEnergy ν μ) ∧
      T.diffeomorphismInvariant ∧
      ∀ μ, T.covariantDivergence μ = 0 := by
  exact ⟨T.symmetric, T.hasDiffeomorphismInvariant,
    T.conserved_of_diffeomorphismInvariant T.hasDiffeomorphismInvariant⟩

end Omega.PhysicalSpacetimeSkeleton
