import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Folding.Defect
import Omega.Folding.FiberEntropySaturation
import Omega.Folding.GaugeAnomalyDensity

namespace Omega.POM

open scoped BigOperators

/-- Concrete POM-side data for the entropy axis, the finite-defect register budget, and the
fold-gauge anomaly witnesses used by the two-axis separation corollary. -/
structure PomTwoAxisSeparationData (m : Nat) where
  visibleCard : Nat
  entropyWeights : Fin visibleCard → ℝ
  fiberMultiplicity : Fin visibleCard → ℕ
  entropyWeights_nonneg : ∀ x, 0 ≤ entropyWeights x
  entropyWeights_sum : ∑ x, entropyWeights x = 1
  fiberMultiplicity_pos : ∀ x, 0 < fiberMultiplicity x
  finiteDefectBudget : Nat
  finiteDefectBudget_eq : finiteDefectBudget = 2 ^ (m - 1)
  anomalyMaxWitness :
    ∃ ω : Omega.Word (m + 1), m ≤ (Finset.univ.filter (fun i => Omega.localDefect ω i = true)).card
  anomalyDensityWitness : Omega.Folding.gStar (1 / 2 : Rat) = 4 / 9

/-- The entropy axis stays controlled by Jensen saturation on the visible fibers. -/
def PomTwoAxisSeparationData.entropyAxisSaturation {m : Nat}
    (h : PomTwoAxisSeparationData m) : Prop :=
  (∑ x, h.entropyWeights x * Real.log (h.fiberMultiplicity x : ℝ)) ≤
    Real.log (∑ x, h.entropyWeights x * h.fiberMultiplicity x)

/-- The corollary packages the entropy-axis saturation together with the finite-defect register
bound and the worst-case / uniform-baseline anomaly witnesses on the rewrite-support axis. -/
def PomTwoAxisSeparationData.twoAxisSeparation {m : Nat}
    (h : PomTwoAxisSeparationData m) : Prop :=
  h.entropyAxisSaturation ∧
    h.finiteDefectBudget = 2 ^ (m - 1) ∧
    (∃ ω : Omega.Word (m + 1),
      m ≤ (Finset.univ.filter (fun i => Omega.localDefect ω i = true)).card) ∧
    Omega.Folding.gStar (1 / 2 : Rat) = 4 / 9

/-- Paper label: `cor:pom-two-axis-separation`. -/
theorem paper_pom_two_axis_separation (m : Nat) (h : PomTwoAxisSeparationData m) :
    h.twoAxisSeparation := by
  have hEntropy :=
    (Omega.Folding.paper_fold_fiber_entropy_saturation h.entropyWeights h.fiberMultiplicity
      h.entropyWeights_nonneg h.entropyWeights_sum h.fiberMultiplicity_pos).1
  exact ⟨hEntropy, h.finiteDefectBudget_eq, h.anomalyMaxWitness, h.anomalyDensityWitness⟩

end Omega.POM
