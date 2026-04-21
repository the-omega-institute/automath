import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Finite cochain package for the exact/cohomological holonomy splitting. -/
structure ObserverHolonomyExactCohomologicalSplittingData where
  Cell : Type
  Edge : Type
  instFintypeCell : Fintype Cell
  instDecEqCell : DecidableEq Cell
  instFintypeEdge : Fintype Edge
  instDecEqEdge : DecidableEq Edge
  sigma : Cell → ℤ
  incidence : Cell → Edge → ℤ
  potential : Edge → ℤ
  anomaly : Cell → ℤ

attribute [instance] ObserverHolonomyExactCohomologicalSplittingData.instFintypeCell
attribute [instance] ObserverHolonomyExactCohomologicalSplittingData.instDecEqCell
attribute [instance] ObserverHolonomyExactCohomologicalSplittingData.instFintypeEdge
attribute [instance] ObserverHolonomyExactCohomologicalSplittingData.instDecEqEdge

namespace ObserverHolonomyExactCohomologicalSplittingData

/-- Boundary coefficients of the finite `2`-chain `Σ`. -/
def boundaryCoeff (D : ObserverHolonomyExactCohomologicalSplittingData) (e : D.Edge) : ℤ :=
  ∑ c, D.sigma c * D.incidence c e

/-- Exact holonomy equals the boundary pairing coming from discrete Stokes. -/
def exactHolonomy (D : ObserverHolonomyExactCohomologicalSplittingData) : ℤ :=
  -∑ e, D.boundaryCoeff e * D.potential e

/-- Pairing of a `2`-cochain with the fixed finite `2`-chain `Σ`. -/
def anomalyHolonomy (D : ObserverHolonomyExactCohomologicalSplittingData) (a : D.Cell → ℤ) : ℤ :=
  ∑ c, D.sigma c * a c

/-- Coboundary correction of a `1`-cochain. -/
def coboundary (D : ObserverHolonomyExactCohomologicalSplittingData) (ξ : D.Edge → ℤ) :
    D.Cell → ℤ :=
  fun c => ∑ e, D.incidence c e * ξ e

/-- Exact measure holonomy vanishes on cycles. -/
def exactMeasureHolonomyVanishesOnCycles (D : ObserverHolonomyExactCohomologicalSplittingData) :
    Prop :=
  (∀ e, D.boundaryCoeff e = 0) → D.exactHolonomy = 0

/-- Adding a coboundary does not change the anomaly holonomy on closed cycles. -/
def anomalyHolonomyFactorsThroughH2 (D : ObserverHolonomyExactCohomologicalSplittingData) :
    Prop :=
  ∀ ξ, (∀ e, D.boundaryCoeff e = 0) →
    D.anomalyHolonomy (fun c => D.anomaly c + D.coboundary ξ c) = D.anomalyHolonomy D.anomaly

lemma anomalyHolonomy_coboundary_eq
    (D : ObserverHolonomyExactCohomologicalSplittingData) (ξ : D.Edge → ℤ) :
    D.anomalyHolonomy (D.coboundary ξ) = ∑ e, D.boundaryCoeff e * ξ e := by
  unfold anomalyHolonomy coboundary boundaryCoeff
  calc
    ∑ c, D.sigma c * ∑ e, D.incidence c e * ξ e
        = ∑ c, ∑ e, D.sigma c * (D.incidence c e * ξ e) := by
            simp_rw [Finset.mul_sum]
    _ = ∑ e, ∑ c, D.sigma c * (D.incidence c e * ξ e) := by
          rw [Finset.sum_comm]
    _ = ∑ e, ∑ c, (D.sigma c * D.incidence c e) * ξ e := by
          simp_rw [mul_assoc]
    _ = ∑ e, (∑ c, D.sigma c * D.incidence c e) * ξ e := by
          simp_rw [Finset.sum_mul]
    _ = ∑ e, D.boundaryCoeff e * ξ e := by
          simp [boundaryCoeff]

lemma exactMeasureHolonomyVanishesOnCycles_proof
    (D : ObserverHolonomyExactCohomologicalSplittingData) :
    D.exactMeasureHolonomyVanishesOnCycles := by
  intro hcycle
  unfold exactHolonomy
  simp [hcycle]

lemma anomalyHolonomyFactorsThroughH2_proof
    (D : ObserverHolonomyExactCohomologicalSplittingData) :
    D.anomalyHolonomyFactorsThroughH2 := by
  intro ξ hcycle
  unfold anomalyHolonomy
  simp_rw [coboundary, mul_add]
  rw [Finset.sum_add_distrib]
  change D.anomalyHolonomy D.anomaly + D.anomalyHolonomy (D.coboundary ξ) = D.anomalyHolonomy D.anomaly
  rw [D.anomalyHolonomy_coboundary_eq ξ]
  simp [hcycle]

end ObserverHolonomyExactCohomologicalSplittingData

open ObserverHolonomyExactCohomologicalSplittingData

/-- Paper-facing exact/cohomological holonomy splitting package.
    thm:conclusion-observer-holonomy-exact-cohomological-splitting -/
theorem paper_conclusion_observer_holonomy_exact_cohomological_splitting
    (D : ObserverHolonomyExactCohomologicalSplittingData) :
    D.exactMeasureHolonomyVanishesOnCycles ∧ D.anomalyHolonomyFactorsThroughH2 := by
  exact ⟨D.exactMeasureHolonomyVanishesOnCycles_proof, D.anomalyHolonomyFactorsThroughH2_proof⟩

end Omega.Conclusion
