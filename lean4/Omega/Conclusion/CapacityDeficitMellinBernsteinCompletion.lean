import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.POM.OracleCapacityStieltjesInversionMellin

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-map data whose fiber multiplicities generate the continuous-capacity, tail,
deficit, and moment objects used in the Mellin--Bernstein completion package. -/
structure ConclusionCapacityDeficitMellinBernsteinData where
  inputSize : Nat
  outputSize : Nat
  map : Fin inputSize → Fin outputSize

/-- Fiber multiplicity profile attached to the finite map. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity
    (h : ConclusionCapacityDeficitMellinBernsteinData) : Fin h.outputSize → ℕ :=
  Omega.POM.oracleFiberMultiplicity h.map

/-- Exact multiplicity histogram. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_histogram
    (h : ConclusionCapacityDeficitMellinBernsteinData) : ℕ → ℕ :=
  fun k =>
    Fintype.card
      {x : Fin h.outputSize //
        conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity h x = k}

/-- Tail-count function. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_tailCount
    (h : ConclusionCapacityDeficitMellinBernsteinData) : ℕ → ℕ :=
  fun t =>
    Fintype.card
      {x : Fin h.outputSize //
        t ≤ conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity h x}

/-- Continuous-capacity curve sampled at integer thresholds. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity
    (h : ConclusionCapacityDeficitMellinBernsteinData) : ℕ → ℕ :=
  Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
    (conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity h)

/-- Capacity deficit against the full input mass. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_deficit
    (h : ConclusionCapacityDeficitMellinBernsteinData) : ℕ → ℕ :=
  fun T =>
    h.inputSize - conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity h T

/-- Discrete moment spectrum of the multiplicity profile. -/
def conclusion_capacity_deficit_mellin_bernstein_completion_momentSpectrum
    (h : ConclusionCapacityDeficitMellinBernsteinData) : ℕ → ℕ :=
  fun q =>
    ∑ x : Fin h.outputSize,
      conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity h x ^ q

/-- The complete package records the oracle-capacity checkpoint, the finite-support equivalence
between histogram/tail/capacity/moment data, and the corresponding deficit identity. -/
def ConclusionCapacityDeficitMellinBernsteinData.completePackage
    (h : ConclusionCapacityDeficitMellinBernsteinData) : Prop :=
  (∀ B : ℕ,
    conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity h (2 ^ B) =
      Omega.POM.bbitOracleCapacity h.map B) ∧
    Omega.Conclusion.FiniteMultiplicityDataEquivalent
      (X := Fin h.outputSize)
      (conclusion_capacity_deficit_mellin_bernstein_completion_histogram h)
      (conclusion_capacity_deficit_mellin_bernstein_completion_tailCount h)
      (conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity h)
      (conclusion_capacity_deficit_mellin_bernstein_completion_momentSpectrum h) ∧
    (∀ T : ℕ,
      conclusion_capacity_deficit_mellin_bernstein_completion_deficit h T =
        h.inputSize -
          conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity h T)

/-- Paper label: `thm:conclusion-capacity-deficit-mellin-bernstein-completion`. -/
theorem paper_conclusion_capacity_deficit_mellin_bernstein_completion
    (h : ConclusionCapacityDeficitMellinBernsteinData) : h.completePackage := by
  have hpkg := Omega.POM.paper_pom_oracle_capacity_stieltjes_inversion_mellin h.map
  refine ⟨hpkg.1, ?_, ?_⟩
  · simpa [conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity,
      conclusion_capacity_deficit_mellin_bernstein_completion_histogram,
      conclusion_capacity_deficit_mellin_bernstein_completion_tailCount,
      conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity,
      conclusion_capacity_deficit_mellin_bernstein_completion_momentSpectrum] using hpkg.2
  · intro T
    rfl

end Omega.Conclusion
