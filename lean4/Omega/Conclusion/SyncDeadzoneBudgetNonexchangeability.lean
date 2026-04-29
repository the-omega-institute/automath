import Omega.SPG.DoubleBudgetAddressCapacity
import Omega.POM.SyncSubtractedChebotarevZeckendorf
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for the sync-deadzone budget comparison. -/
structure ConclusionSyncDeadzoneBudgetNonexchangeabilityData where
  m : ℕ
  n : ℕ
  groupCard : ℕ
  epsilonAddr : ℝ
  u : ℝ
  lambdaValue : ℝ
  epsilonGap : ℝ
  deltaCheb : ℝ
  hm : 3 ≤ m
  hsync : n < m - 1
  hcard : 1 ≤ groupCard
  hlambda : 0 < lambdaValue
  hdelta : 0 < deltaCheb
  hdelta_le_one : deltaCheb ≤ 1
  hRelativeError :
    (groupCard : ℝ) ≤
      deltaCheb * lambdaValue ^ ((((1 / 2 : ℝ) + epsilonGap) * ((n + 1 - m : Nat) : ℝ)))
  haddr_pos : 0 < min (epsilonAddr * n) (((1 / 2 : ℝ) * u) * m)

namespace ConclusionSyncDeadzoneBudgetNonexchangeabilityData

/-- Address budget available before arithmetic synchronization constraints are imposed. -/
def conclusion_sync_deadzone_budget_nonexchangeability_addressBudget
    (D : ConclusionSyncDeadzoneBudgetNonexchangeabilityData) : ℝ :=
  min (D.epsilonAddr * D.n) (((1 / 2 : ℝ) * D.u) * D.m)

/-- Synchronization-subtracted Chebotarev budget in the Zeckendorf specialization. -/
def conclusion_sync_deadzone_budget_nonexchangeability_syncBudget
    (D : ConclusionSyncDeadzoneBudgetNonexchangeabilityData) : ℝ :=
  Omega.POM.pom_sync_subtracted_chebotarev_capacity_budget D.lambdaValue D.epsilonGap D.deltaCheb
    (D.n + 1 - D.m)

/-- Paper-facing deadzone/nonexchangeability package. -/
def holds (D : ConclusionSyncDeadzoneBudgetNonexchangeabilityData) : Prop :=
  ((∀ m, 1 ≤ m → 2 * Nat.fib (m + 2) > Nat.fib (m + 3)) ∧
      (2 * Nat.fib 4 > Nat.fib 5) ∧
      (2 * Nat.fib 7 > Nat.fib 8) ∧
      (2 * Nat.fib 12 > Nat.fib 13)) ∧
    Real.log (D.groupCard : ℝ) ≤
      D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget ∧
    D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget ≤ 0 ∧
    0 < D.conclusion_sync_deadzone_budget_nonexchangeability_addressBudget ∧
    min D.conclusion_sync_deadzone_budget_nonexchangeability_addressBudget
        D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget =
      D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget ∧
    D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget <
      D.conclusion_sync_deadzone_budget_nonexchangeability_addressBudget

lemma conclusion_sync_deadzone_budget_nonexchangeability_syncBudget_eq_log_delta
    (D : ConclusionSyncDeadzoneBudgetNonexchangeabilityData) :
    D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget = Real.log D.deltaCheb := by
  have hle : D.n + 1 ≤ D.m := by
    exact le_trans (Nat.succ_le_of_lt D.hsync) (Nat.sub_le D.m 1)
  have hdepth : D.n + 1 - D.m = 0 := Nat.sub_eq_zero_of_le hle
  unfold conclusion_sync_deadzone_budget_nonexchangeability_syncBudget
    Omega.POM.pom_sync_subtracted_chebotarev_capacity_budget
  rw [hdepth]
  have hloginv : Real.log (1 / D.deltaCheb) = -Real.log D.deltaCheb := by
    simp [one_div, Real.log_inv]
  rw [hloginv]
  ring

end ConclusionSyncDeadzoneBudgetNonexchangeabilityData

open ConclusionSyncDeadzoneBudgetNonexchangeabilityData

/-- Paper label: `thm:conclusion-sync-deadzone-budget-nonexchangeability`. -/
theorem paper_conclusion_sync_deadzone_budget_nonexchangeability
    (D : ConclusionSyncDeadzoneBudgetNonexchangeabilityData) : D.holds := by
  have hsyncBound :
      Real.log (D.groupCard : ℝ) ≤ D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget := by
    simpa [conclusion_sync_deadzone_budget_nonexchangeability_syncBudget] using
      Omega.POM.paper_pom_sync_subtracted_chebotarev_zeckendorf D.n D.m D.groupCard D.lambdaValue
        D.epsilonGap D.deltaCheb D.hm D.hcard D.hlambda D.hdelta D.hRelativeError
  have hsyncNonpos :
      D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget ≤ 0 := by
    rw [D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget_eq_log_delta]
    exact Real.log_nonpos (le_of_lt D.hdelta) D.hdelta_le_one
  have hsyncLtAddr :
      D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget <
        D.conclusion_sync_deadzone_budget_nonexchangeability_addressBudget :=
    lt_of_le_of_lt hsyncNonpos D.haddr_pos
  have hminEq :
      min D.conclusion_sync_deadzone_budget_nonexchangeability_addressBudget
          D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget =
        D.conclusion_sync_deadzone_budget_nonexchangeability_syncBudget := by
    exact min_eq_right (le_of_lt hsyncLtAddr)
  exact ⟨Omega.SPG.paper_spg_double_budget_address_capacity.1, hsyncBound, hsyncNonpos,
    D.haddr_pos, hminEq, hsyncLtAddr⟩

end

end Omega.Conclusion
