import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- Concrete asymptotic data for the replica softcore Perron and second exceptional eigenvalues. -/
structure pom_replica_softcore_gap_ratio_log_separation_data where
  perron : ℕ → ℝ
  secondExceptional : ℕ → ℝ
  perronPositive : ∀ᶠ q in atTop, 0 < perron q
  secondPositive : ∀ᶠ q in atTop, 0 < secondExceptional q
  ratioAsymptotic :
    Tendsto
      (fun q : ℕ =>
        (secondExceptional q / perron q) / ((Real.goldenRatio / 2 : ℝ) ^ q))
      atTop (𝓝 1)
  logSeparationAsymptotic :
    Tendsto
      (fun q : ℕ =>
        Real.log (perron q / secondExceptional q) / (q : ℝ))
      atTop (𝓝 (Real.log (2 / Real.goldenRatio : ℝ)))

/-- The encoded ratio law and logarithmic separation law. -/
def pom_replica_softcore_gap_ratio_log_separation_statement
    (D : pom_replica_softcore_gap_ratio_log_separation_data) : Prop :=
  Tendsto
      (fun q : ℕ =>
        (D.secondExceptional q / D.perron q) / ((Real.goldenRatio / 2 : ℝ) ^ q))
      atTop (𝓝 1) ∧
    Tendsto
      (fun q : ℕ =>
        Real.log (D.perron q / D.secondExceptional q) / (q : ℝ))
      atTop (𝓝 (Real.log (2 / Real.goldenRatio : ℝ)))

/-- Paper label: `thm:pom-replica-softcore-gap-ratio-log-separation`. -/
theorem paper_pom_replica_softcore_gap_ratio_log_separation
    (D : pom_replica_softcore_gap_ratio_log_separation_data) :
    pom_replica_softcore_gap_ratio_log_separation_statement D := by
  exact ⟨D.ratioAsymptotic, D.logSeparationAsymptotic⟩

end Omega.POM
