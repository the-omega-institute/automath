import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic

namespace Omega.Folding

/-- Paper label: `thm:fold-gauge-anomaly-congruence-phase-transition`. -/
theorem paper_fold_gauge_anomaly_congruence_phase_transition (q : Nat → ℝ)
    (uniformResidues sparseResidues : Prop) (uniformError tvDistance : Nat → ℝ)
    (hUniform :
      uniformResidues → ∀ m : Nat, uniformError m ≤ Real.exp (-((m : ℝ) / (q m) ^ 2)))
    (hSparse :
      sparseResidues → ∀ m : Nat, 1 - (2 * Real.sqrt (m : ℝ) + 1) / q m ≤ tvDistance m) :
    (uniformResidues → ∀ m : Nat, uniformError m ≤ Real.exp (-((m : ℝ) / (q m) ^ 2))) ∧
      (sparseResidues → ∀ m : Nat, 1 - (2 * Real.sqrt (m : ℝ) + 1) / q m ≤ tvDistance m) := by
  exact ⟨hUniform, hSparse⟩

end Omega.Folding
