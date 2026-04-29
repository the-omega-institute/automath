import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped Topology

noncomputable section

/-- Concrete data for the replay-Godel sharp strong converse.  The sequences record the
history lower scale, the available replay budget, the logarithmic budget certificate, the
probability of the high-history event, and the success probability of the replay procedure. -/
structure conclusion_replay_godel_sharp_strong_converse_data where
  conclusion_replay_godel_sharp_strong_converse_gHist : ℕ → ℝ
  conclusion_replay_godel_sharp_strong_converse_budgetMass : ℕ → ℝ
  conclusion_replay_godel_sharp_strong_converse_logBudget : ℕ → ℝ
  conclusion_replay_godel_sharp_strong_converse_highHistoryProb : ℕ → ℝ
  conclusion_replay_godel_sharp_strong_converse_successProb : ℕ → ℝ
  conclusion_replay_godel_sharp_strong_converse_delta : ℝ
  conclusion_replay_godel_sharp_strong_converse_delta_pos :
    0 < conclusion_replay_godel_sharp_strong_converse_delta
  conclusion_replay_godel_sharp_strong_converse_delta_lt :
    conclusion_replay_godel_sharp_strong_converse_delta < (4 / 27 : ℝ)
  conclusion_replay_godel_sharp_strong_converse_logBudget_control :
    ∀ᶠ m : ℕ in atTop,
      conclusion_replay_godel_sharp_strong_converse_logBudget m ≤
        ((4 / 27 : ℝ) - conclusion_replay_godel_sharp_strong_converse_delta) *
          (m : ℝ)
  conclusion_replay_godel_sharp_strong_converse_budget_half_le_log :
    ∀ᶠ m : ℕ in atTop,
      conclusion_replay_godel_sharp_strong_converse_budgetMass m / 2 ≤
        conclusion_replay_godel_sharp_strong_converse_logBudget m
  conclusion_replay_godel_sharp_strong_converse_history_lower :
    ∀ᶠ m : ℕ in atTop,
      ((4 / 27 : ℝ) - conclusion_replay_godel_sharp_strong_converse_delta / 2) *
          (m : ℝ) ≤
        conclusion_replay_godel_sharp_strong_converse_gHist m
  conclusion_replay_godel_sharp_strong_converse_highHistory_tendsto_one :
    Tendsto conclusion_replay_godel_sharp_strong_converse_highHistoryProb atTop (𝓝 1)
  conclusion_replay_godel_sharp_strong_converse_success_nonneg :
    ∀ᶠ m : ℕ in atTop,
      0 ≤ conclusion_replay_godel_sharp_strong_converse_successProb m
  conclusion_replay_godel_sharp_strong_converse_success_le_complement_of_gap :
    ∀ᶠ m : ℕ in atTop,
      conclusion_replay_godel_sharp_strong_converse_gHist m >
          conclusion_replay_godel_sharp_strong_converse_budgetMass m / 2 →
        conclusion_replay_godel_sharp_strong_converse_successProb m ≤
          1 - conclusion_replay_godel_sharp_strong_converse_highHistoryProb m

/-- Claim extracted from the strong converse: success vanishes, hence the failure probability
tends to one. -/
def conclusion_replay_godel_sharp_strong_converse_claim
    (D : conclusion_replay_godel_sharp_strong_converse_data) : Prop :=
  Tendsto D.conclusion_replay_godel_sharp_strong_converse_successProb atTop (𝓝 0) ∧
    Tendsto
      (fun m : ℕ => 1 - D.conclusion_replay_godel_sharp_strong_converse_successProb m)
      atTop (𝓝 1)

/-- Paper label: `thm:conclusion-replay-godel-sharp-strong-converse`. -/
theorem paper_conclusion_replay_godel_sharp_strong_converse
    (D : conclusion_replay_godel_sharp_strong_converse_data) :
    conclusion_replay_godel_sharp_strong_converse_claim D := by
  have hgap :
      ∀ᶠ m : ℕ in atTop,
        D.conclusion_replay_godel_sharp_strong_converse_gHist m >
          D.conclusion_replay_godel_sharp_strong_converse_budgetMass m / 2 := by
    filter_upwards
      [D.conclusion_replay_godel_sharp_strong_converse_logBudget_control,
        D.conclusion_replay_godel_sharp_strong_converse_budget_half_le_log,
        D.conclusion_replay_godel_sharp_strong_converse_history_lower,
        eventually_ge_atTop 1] with m hlog hhalf hlower hm
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmargin :
        ((4 / 27 : ℝ) - D.conclusion_replay_godel_sharp_strong_converse_delta) *
            (m : ℝ) <
          ((4 / 27 : ℝ) -
              D.conclusion_replay_godel_sharp_strong_converse_delta / 2) *
            (m : ℝ) := by
      nlinarith [D.conclusion_replay_godel_sharp_strong_converse_delta_pos, hm_pos]
    exact lt_of_le_of_lt hhalf (lt_of_le_of_lt hlog (lt_of_lt_of_le hmargin hlower))
  have hupper :
      ∀ᶠ m : ℕ in atTop,
        D.conclusion_replay_godel_sharp_strong_converse_successProb m ≤
          1 - D.conclusion_replay_godel_sharp_strong_converse_highHistoryProb m := by
    filter_upwards
      [hgap, D.conclusion_replay_godel_sharp_strong_converse_success_le_complement_of_gap] with
      m hgap_m hsuccess
    exact hsuccess hgap_m
  have hcomplement_zero :
      Tendsto
        (fun m : ℕ => 1 - D.conclusion_replay_godel_sharp_strong_converse_highHistoryProb m)
        atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        D.conclusion_replay_godel_sharp_strong_converse_highHistory_tendsto_one)
  have hsuccess_zero :
      Tendsto D.conclusion_replay_godel_sharp_strong_converse_successProb atTop (𝓝 0) :=
    squeeze_zero'
      D.conclusion_replay_godel_sharp_strong_converse_success_nonneg hupper hcomplement_zero
  refine ⟨hsuccess_zero, ?_⟩
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsuccess_zero)

end

end Omega.Conclusion
