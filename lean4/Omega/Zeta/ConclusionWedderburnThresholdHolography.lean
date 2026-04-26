import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.CapacityDeficitMellinBernsteinCompletion

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite map data for the Wedderburn-threshold holography package. The semisimple
class is encoded by the same block-size histogram as the fiber multiplicity profile. -/
structure conclusion_wedderburn_threshold_holography_data where
  inputSize : ℕ
  outputSize : ℕ
  map : Fin inputSize → Fin outputSize

namespace conclusion_wedderburn_threshold_holography_data

def toCapacityData (D : conclusion_wedderburn_threshold_holography_data) :
    Omega.Conclusion.ConclusionCapacityDeficitMellinBernsteinData where
  inputSize := D.inputSize
  outputSize := D.outputSize
  map := D.map

def fiberMultiplicity (D : conclusion_wedderburn_threshold_holography_data) :
    Fin D.outputSize → ℕ :=
  Omega.Conclusion.conclusion_capacity_deficit_mellin_bernstein_completion_fiberMultiplicity
    (toCapacityData D)

def capacityCurve (D : conclusion_wedderburn_threshold_holography_data) : ℕ → ℕ :=
  Omega.Conclusion.conclusion_capacity_deficit_mellin_bernstein_completion_continuousCapacity
    (toCapacityData D)

def tailCounts (D : conclusion_wedderburn_threshold_holography_data) : ℕ → ℕ :=
  Omega.Conclusion.conclusion_capacity_deficit_mellin_bernstein_completion_tailCount
    (toCapacityData D)

def histogram (D : conclusion_wedderburn_threshold_holography_data) : ℕ → ℕ :=
  Omega.Conclusion.conclusion_capacity_deficit_mellin_bernstein_completion_histogram
    (toCapacityData D)

def wedderburnClass (D : conclusion_wedderburn_threshold_holography_data) : ℕ → ℕ :=
  D.histogram

def capacityCurveDeterminesTailCounts (D : conclusion_wedderburn_threshold_holography_data) :
    Prop :=
  ∀ t, 1 ≤ t → D.tailCounts t = D.capacityCurve t - D.capacityCurve (t - 1)

def tailCountsDetermineHistogram (D : conclusion_wedderburn_threshold_holography_data) : Prop :=
  ∀ k, D.histogram k = D.tailCounts k - D.tailCounts (k + 1)

def histogramDeterminesWedderburnClass
    (D : conclusion_wedderburn_threshold_holography_data) : Prop :=
  D.wedderburnClass = D.histogram

end conclusion_wedderburn_threshold_holography_data

open conclusion_wedderburn_threshold_holography_data

/-- Paper label: `thm:conclusion-wedderburn-threshold-holography`. The existing finite-capacity
reconstruction theorem gives the capacity-curve/tail-count/histogram equivalence, and the
semisimple Wedderburn class is recorded by the same block-size histogram. -/
theorem paper_conclusion_wedderburn_threshold_holography
    (D : conclusion_wedderburn_threshold_holography_data) :
    D.capacityCurveDeterminesTailCounts ∧
      D.tailCountsDetermineHistogram ∧
      D.histogramDeterminesWedderburnClass := by
  let d : Fin D.outputSize → ℕ := D.fiberMultiplicity
  have hpkg := Omega.Conclusion.paper_conclusion_capacity_finite_completeness
    (X := Fin D.outputSize) d
  dsimp [Omega.Conclusion.FiniteMultiplicityDataEquivalent] at hpkg
  rcases hpkg with ⟨M, hM, htail, hhist, hmoment⟩
  refine ⟨?_, ?_, rfl⟩
  · intro t ht
    simpa [d, conclusion_wedderburn_threshold_holography_data.capacityCurveDeterminesTailCounts,
      conclusion_wedderburn_threshold_holography_data.tailCounts,
      conclusion_wedderburn_threshold_holography_data.capacityCurve] using htail t ht
  · intro k
    simpa [d, conclusion_wedderburn_threshold_holography_data.tailCountsDetermineHistogram,
      conclusion_wedderburn_threshold_holography_data.histogram,
      conclusion_wedderburn_threshold_holography_data.tailCounts] using hhist k

end Omega.Zeta
