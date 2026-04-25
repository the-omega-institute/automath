import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- The successful AE-recovery budgets: nonnegative rates whose floor-budget success profile tends
to `1`. -/
def conclusion_ae_recovery_threshold_sandwich_budgetSet (Succ : ℕ → ℕ → ℝ) : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ Tendsto (fun m : ℕ => Succ m ⌊β * m⌋₊) atTop (nhds 1)}

/-- The AE-recovery threshold is the infimum of all successful budgets. -/
noncomputable def conclusion_ae_recovery_threshold_sandwich_betaAe (Succ : ℕ → ℕ → ℝ) : ℝ :=
  sInf (conclusion_ae_recovery_threshold_sandwich_budgetSet Succ)

/-- The universal golden-ratio lower bound `1 - log₂ φ`. -/
noncomputable def conclusion_ae_recovery_threshold_sandwich_goldenLower : ℝ :=
  1 - Real.log Real.goldenRatio / Real.log 2

/-- Paper-facing threshold sandwich: the AE threshold is defined as an infimum over successful
budgets, every successful budget inherits the universal pigeonhole lower bound, and once the
second-maximum recovery window is available the infimum is bounded above by `α_*^(2) / log 2`. -/
def conclusion_ae_recovery_threshold_sandwich_statement : Prop :=
  ∀ (Succ : ℕ → ℕ → ℝ) (alphaStar alphaTwo gStar : ℝ),
    Set.Nonempty (conclusion_ae_recovery_threshold_sandwich_budgetSet Succ) →
    (∀ β : ℝ, β ∈ conclusion_ae_recovery_threshold_sandwich_budgetSet Succ →
      conclusion_ae_recovery_threshold_sandwich_goldenLower ≤ β) →
    (alphaStar + gStar < Real.log 2 →
      ∀ β : ℝ, alphaTwo / Real.log 2 < β →
        β ∈ conclusion_ae_recovery_threshold_sandwich_budgetSet Succ) →
      conclusion_ae_recovery_threshold_sandwich_goldenLower ≤
          conclusion_ae_recovery_threshold_sandwich_betaAe Succ ∧
        (alphaStar + gStar < Real.log 2 →
          conclusion_ae_recovery_threshold_sandwich_betaAe Succ ≤ alphaTwo / Real.log 2)

theorem paper_conclusion_ae_recovery_threshold_sandwich :
    conclusion_ae_recovery_threshold_sandwich_statement := by
  intro Succ alphaStar alphaTwo gStar hnonempty hpigeonhole hsecond
  have hbdd :
      BddBelow (conclusion_ae_recovery_threshold_sandwich_budgetSet Succ) := by
    refine ⟨0, ?_⟩
    intro β hβ
    exact hβ.1
  refine ⟨?_, ?_⟩
  · unfold conclusion_ae_recovery_threshold_sandwich_betaAe
    exact le_csInf hnonempty (fun β hβ => hpigeonhole β hβ)
  · intro hgap
    unfold conclusion_ae_recovery_threshold_sandwich_betaAe
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    have hmem :
        alphaTwo / Real.log 2 + ε ∈ conclusion_ae_recovery_threshold_sandwich_budgetSet Succ := by
      exact hsecond hgap (alphaTwo / Real.log 2 + ε) (by linarith)
    exact csInf_le hbdd hmem

end Omega.Conclusion
