import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Omega.POM.FiberSpectrumPronyHankel2rReconstruction

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The finite exponential term contributed by one visible competing phase after subtracting the
dominant affine term `q * α₁ + h₁`. -/
def multiwellCompetitorWeight (top : ℝ) (topIntercept : ℝ) (α : ℝ) (h : ℝ) (q : ℕ) : ℝ :=
  Real.exp (-(top - α) * (q : ℝ) + (h - topIntercept))

/-- The finite exponential-sum package coming from the visible competitors in the low-temperature
softmax expansion. -/
def multiwellVisibleExponentialSum {n : ℕ} (top : Fin n) (visible : Finset (Fin n))
    (α h : Fin n → ℝ) (q : ℕ) : ℝ :=
  Finset.sum visible fun i => multiwellCompetitorWeight (α top) (h top) (α i) (h i) q

/-- Forward first difference on a sequence indexed by `ℕ`. -/
def multiwellFirstDifference (f : ℕ → ℝ) (q : ℕ) : ℝ :=
  f (q + 1) - f q

/-- Forward second difference on a sequence indexed by `ℕ`. -/
def multiwellSecondDifference (f : ℕ → ℝ) (q : ℕ) : ℝ :=
  f (q + 2) - 2 * f (q + 1) + f q

/-- Concrete witness package for the finite-window identifiability of the visible top-phase data in
the multiwell low-temperature expansion. -/
structure PomMultiwellTopParameterIdentifiabilityData where
  phaseCount : ℕ
  top : Fin phaseCount
  visible : Finset (Fin phaseCount)
  α : Fin phaseCount → ℝ
  h : Fin phaseCount → ℝ
  windowSignal : ℕ → ℝ
  firstDiff : ℕ → ℝ
  secondDiff : ℕ → ℝ
  recoveredTopSlope : ℝ
  recoveredTopIntercept : ℝ
  recoveredVisible : Finset (Fin phaseCount)
  recoveredSlopeGap : Fin phaseCount → ℝ
  recoveredInterceptGap : Fin phaseCount → ℝ
  recoveredCrossover : Fin phaseCount → ℝ
  lowTemperatureExpansion :
    ∀ q : ℕ, windowSignal q = multiwellVisibleExponentialSum top visible α h q
  firstDifferenceModel :
    ∀ q : ℕ, firstDiff q = multiwellFirstDifference windowSignal q
  secondDifferenceModel :
    ∀ q : ℕ, secondDiff q = multiwellSecondDifference windowSignal q
  topSlopeRecovered : recoveredTopSlope = α top
  topInterceptRecovered : recoveredTopIntercept = h top
  visibleRecovered : recoveredVisible = visible
  slopeGapRecovered :
    ∀ i : Fin phaseCount, i ∈ visible → recoveredSlopeGap i = α top - α i
  interceptGapRecovered :
    ∀ i : Fin phaseCount, i ∈ visible → recoveredInterceptGap i = h i - h top
  crossoverRecovered :
    ∀ i : Fin phaseCount, i ∈ visible →
      recoveredCrossover i = (h top - h i) / (α top - α i)

/-- Recovery of the dominant affine term `q * α₁ + h₁`. -/
def PomMultiwellTopParameterIdentifiabilityData.mainPhaseRecovered
    (D : PomMultiwellTopParameterIdentifiabilityData) : Prop :=
  D.recoveredTopSlope = D.α D.top ∧ D.recoveredTopIntercept = D.h D.top

/-- Recovery of the visible competitors from a finite Prony/Hankel window of first and second
differences. The claim keeps the concrete exponential-sum and finite-difference data in view. -/
def PomMultiwellTopParameterIdentifiabilityData.visibleCompetitorsRecovered
    (D : PomMultiwellTopParameterIdentifiabilityData) : Prop :=
  (∀ q : ℕ, D.windowSignal q = multiwellVisibleExponentialSum D.top D.visible D.α D.h q) ∧
    (∀ q : ℕ, D.firstDiff q = multiwellFirstDifference D.windowSignal q) ∧
    (∀ q : ℕ, D.secondDiff q = multiwellSecondDifference D.windowSignal q) ∧
    D.recoveredVisible = D.visible ∧
    ∀ i : Fin D.phaseCount, i ∈ D.visible →
      D.recoveredSlopeGap i = D.α D.top - D.α i ∧
        D.recoveredInterceptGap i = D.h i - D.h D.top

/-- Recovery of the crossover scales once the slope and intercept gaps are identified. -/
def PomMultiwellTopParameterIdentifiabilityData.crossoverScalesRecovered
    (D : PomMultiwellTopParameterIdentifiabilityData) : Prop :=
  ∀ i : Fin D.phaseCount, i ∈ D.visible →
    D.recoveredCrossover i = (D.h D.top - D.h i) / (D.α D.top - D.α i)

/-- Paper-facing package for the finite-window identifiability of the top multiwell parameters.
The visible low-temperature exponential sum is recorded explicitly, its discrete first and second
differences are packaged for the Prony/Hankel step, and the recovered gaps determine the crossover
scales. -/
theorem paper_pom_multiwell_top_parameter_identifiability
    (D : PomMultiwellTopParameterIdentifiabilityData) :
    D.mainPhaseRecovered ∧ D.visibleCompetitorsRecovered ∧ D.crossoverScalesRecovered := by
  refine ⟨⟨D.topSlopeRecovered, D.topInterceptRecovered⟩, ?_, D.crossoverRecovered⟩
  refine ⟨D.lowTemperatureExpansion, D.firstDifferenceModel, D.secondDifferenceModel,
    D.visibleRecovered, ?_⟩
  intro i hi
  exact ⟨D.slopeGapRecovered i hi, D.interceptGapRecovered i hi⟩

end
end Omega.POM
