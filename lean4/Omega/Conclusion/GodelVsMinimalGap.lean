import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Uniform-source entropy at resolution `m`. -/
def uniformSourceEntropy (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log 2

/-- Fiber budget `H(A|X)` obtained from the chain-rule identity
`H(A) = H(X) + H(A|X)` under the uniform baseline. -/
def fiberBudget (m : ℕ) (observableEntropy : ℝ) : ℝ :=
  uniformSourceEntropy m - observableEntropy

/-- Concrete entropy-budget data for the Godel-vs-minimal-gap comparison. -/
structure GodelVsMinimalGapData where
  m : ℕ
  hm : 1 ≤ m
  XCard : ℕ
  hXCard_pos : 0 < XCard
  observableEntropy : ℝ
  recordConditionalEntropy : ℝ
  historyGrowth : ℝ
  hInjective :
    fiberBudget m observableEntropy ≤ recordConditionalEntropy
  hObservable_nonneg : 0 ≤ observableEntropy
  hObservable_card :
    observableEntropy ≤ Real.log (XCard : ℝ)
  hFibBound : XCard ≤ Nat.fib (m + 2)
  hRecordUpper :
    recordConditionalEntropy ≤ uniformSourceEntropy m
  hHistoryGrowth :
    (m : ℝ) * Real.log (m + 2 : ℝ) ≤ historyGrowth

namespace GodelVsMinimalGapData

/-- Injective replay side information dominates the conditional fiber budget. -/
def minimalInformationLowerBound (D : GodelVsMinimalGapData) : Prop :=
  fiberBudget D.m D.observableEntropy ≤ D.recordConditionalEntropy

/-- The fiber budget has the explicit linear lower bound obtained from `|X_m| ≤ F_{m+2}`. -/
def linearFiberBudgetLowerBound (D : GodelVsMinimalGapData) : Prop :=
  uniformSourceEntropy D.m - Real.log (Nat.fib (D.m + 2) : ℝ) ≤ D.recordConditionalEntropy

/-- Replayable histories cost at least the information-reversible budget. -/
def replayOverheadGap (D : GodelVsMinimalGapData) : Prop :=
  D.recordConditionalEntropy ≤ D.historyGrowth

lemma minimal_information_lower_bound (D : GodelVsMinimalGapData) :
    D.minimalInformationLowerBound := D.hInjective

lemma linear_fiber_budget_lower_bound (D : GodelVsMinimalGapData) :
    D.linearFiberBudgetLowerBound := by
  have hX_pos : (0 : ℝ) < (D.XCard : ℝ) := by
    exact_mod_cast D.hXCard_pos
  have hFib_pos : (0 : ℝ) < (Nat.fib (D.m + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hlog_card :
      Real.log (D.XCard : ℝ) ≤ Real.log (Nat.fib (D.m + 2) : ℝ) := by
    exact Real.log_le_log hX_pos (by exact_mod_cast D.hFibBound)
  have hstep1 :
      uniformSourceEntropy D.m - Real.log (Nat.fib (D.m + 2) : ℝ) ≤
        uniformSourceEntropy D.m - Real.log (D.XCard : ℝ) := by
    linarith
  have hstep2 :
      uniformSourceEntropy D.m - Real.log (D.XCard : ℝ) ≤
        fiberBudget D.m D.observableEntropy := by
    unfold fiberBudget uniformSourceEntropy
    linarith [D.hObservable_card]
  exact le_trans hstep1 (le_trans hstep2 D.hInjective)

lemma replay_overhead_gap (D : GodelVsMinimalGapData) :
    D.replayOverheadGap := by
  have hm_nonneg : (0 : ℝ) ≤ D.m := by positivity
  have hlog :
      Real.log 2 ≤ Real.log (D.m + 2 : ℝ) := by
    have htwo : (2 : ℝ) ≤ D.m + 2 := by
      have : (1 : ℝ) ≤ D.m := by exact_mod_cast D.hm
      linarith
    exact Real.log_le_log (by positivity) htwo
  have huniform :
      uniformSourceEntropy D.m ≤ (D.m : ℝ) * Real.log (D.m + 2 : ℝ) := by
    unfold uniformSourceEntropy
    exact mul_le_mul_of_nonneg_left hlog hm_nonneg
  exact le_trans D.hRecordUpper (le_trans huniform D.hHistoryGrowth)

end GodelVsMinimalGapData

open GodelVsMinimalGapData

/-- Paper-facing package for the entropy-gap comparison between injective information recovery and
replayable Godel histories.
    thm:conclusion-godel-vs-minimal-gap -/
theorem paper_conclusion_godel_vs_minimal_gap (D : GodelVsMinimalGapData) :
    D.minimalInformationLowerBound ∧ D.linearFiberBudgetLowerBound ∧ D.replayOverheadGap := by
  exact ⟨D.minimal_information_lower_bound, D.linear_fiber_budget_lower_bound,
    D.replay_overhead_gap⟩

end

end Omega.Conclusion
