import Mathlib
import Omega.Conclusion.BoundaryStokesStrictLinearHolography
import Omega.Conclusion.FixedResolutionAxialScreenCorankAreaLaw
import Omega.Conclusion.FixedResolutionScreenCorankAuditCostLaw
import Omega.Conclusion.LocalizedSolenoidCoprimeArtinMazurCompleteness

namespace Omega.Conclusion

/-- Data parameter for the fixed-resolution holography double-obstruction synthesis. -/
structure conclusion_fixedresolution_holography_double_obstruction_synthesis_data where

/-- Geometric obstruction package: strict linear holography, exact corank audit cost, the axial
area law, and supermodularity of the corank-style audit gap. -/
def conclusion_fixedresolution_holography_double_obstruction_synthesis_geometric
    {V : Type*} [DecidableEq V] (m n ρ : ℕ) (r : Finset V → ℕ) : Prop :=
  Function.Bijective (boundaryStokesStrictLinearHolography m n) ∧
    fixedResolutionScreenAuditCost m n = fixedResolutionScreenKernelRank m n ∧
    fixedResolutionScreenAuditCost m n = 2 ^ (m * (n - 1)) ∧
    fixedResolutionScreenSupermodular ρ r

/-- Arithmetic obstruction package: Artin-Mazur separation is equivalent both to periodic-count
separation and to the gcd-one criterion for the chosen localization family. -/
def conclusion_fixedresolution_holography_double_obstruction_synthesis_arithmetic
    (F : LocalizedSolenoidBaseFamily) : Prop :=
  (periodicCountsSeparate F ↔ zetaFamilySeparates F) ∧
    (periodicCountsSeparate F ↔ gcdBasesEqOne F)

/-- Paper-facing statement for the conclusion-level double-obstruction synthesis. -/
def conclusion_fixedresolution_holography_double_obstruction_synthesis_statement
    (_D : conclusion_fixedresolution_holography_double_obstruction_synthesis_data) : Prop :=
  ∀ {V : Type*} [DecidableEq V] (m n ρ : ℕ) (r : Finset V → ℕ)
      (F : LocalizedSolenoidBaseFamily),
    1 ≤ m →
      1 ≤ n →
        (∀ s, r s ≤ ρ) →
          (∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) →
            conclusion_fixedresolution_holography_double_obstruction_synthesis_geometric m n ρ r ∧
              conclusion_fixedresolution_holography_double_obstruction_synthesis_arithmetic F

/-- Paper label:
`thm:conclusion-fixedresolution-holography-double-obstruction-synthesis`. -/
theorem paper_conclusion_fixedresolution_holography_double_obstruction_synthesis
    (D : conclusion_fixedresolution_holography_double_obstruction_synthesis_data) :
    conclusion_fixedresolution_holography_double_obstruction_synthesis_statement D := by
  intro V _ m n ρ r F hm hn hρ hsub
  have hHolo := paper_conclusion_boundary_stokes_strict_linear_holography m n
  have hScreen :=
    paper_conclusion_fixedresolution_screen_corank_audit_cost_law m n ρ r hm hn hρ hsub
  have hArea := paper_conclusion_fixedresolution_axial_screen_corank_area_law m n
  have hArtin := paper_conclusion_localized_solenoid_coprime_artin_mazur_completeness F
  refine ⟨?_, hArtin⟩
  exact ⟨hHolo.2, hScreen.1, hArea, hScreen.2.2.2.2.1⟩

end Omega.Conclusion
