import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.POM.ProfiniteCylinderCapacity

namespace Omega.POM

/-- Synchronization deduction entering the time budget. -/
def pom_sync_subtracted_chebotarev_capacity_n_sync {α : Type*}
    (ambiguityShell : Finset α) (syncDelay syncTailBudget : ℕ) : ℕ :=
  if ambiguityShell.card = 0 then syncDelay else syncTailBudget

/-- Effective depth after subtracting the synchronization deduction. -/
def pom_sync_subtracted_chebotarev_capacity_n_eff {α : Type*}
    (ambiguityShell : Finset α) (n syncDelay syncTailBudget : ℕ) : ℕ :=
  n - pom_sync_subtracted_chebotarev_capacity_n_sync ambiguityShell syncDelay syncTailBudget

/-- Capacity budget evaluated at an effective depth. -/
noncomputable def pom_sync_subtracted_chebotarev_capacity_budget
    (lambdaValue epsilonGap deltaCheb : ℝ) (nEff : ℕ) : ℝ :=
  (((1 / 2 : ℝ) + epsilonGap) * (nEff : ℝ)) * Real.log lambdaValue - Real.log (1 / deltaCheb)

/-- The synchronization-subtracted Chebotarev capacity law is the profinite-cylinder capacity
estimate evaluated at `n_eff = (n - n_sync)_+`, together with the two case-split rewrites for the
empty and nonempty ambiguity shell.
    thm:pom-sync-subtracted-chebotarev-capacity -/
theorem paper_pom_sync_subtracted_chebotarev_capacity
    {α : Type*} [DecidableEq α] (ambiguityShell : Finset α)
    (n syncDelay syncTailBudget groupCard : ℕ)
    (lambdaValue epsilonGap deltaCheb : ℝ)
    (hcard : 1 ≤ groupCard) (hlambda : 0 < lambdaValue) (hdelta : 0 < deltaCheb)
    (hRelativeError :
      (groupCard : ℝ) ≤
        deltaCheb *
          lambdaValue ^
            (((1 / 2 : ℝ) + epsilonGap) *
              (pom_sync_subtracted_chebotarev_capacity_n_eff
                ambiguityShell n syncDelay syncTailBudget : ℝ))) :
    Real.log (groupCard : ℝ) ≤
        pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb
          (pom_sync_subtracted_chebotarev_capacity_n_eff ambiguityShell n syncDelay syncTailBudget) ∧
      (ambiguityShell.card = 0 →
        Real.log (groupCard : ℝ) ≤
          pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb
            (n - syncDelay)) ∧
      (ambiguityShell.card ≠ 0 →
        Real.log (groupCard : ℝ) ≤
          pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb
            (n - syncTailBudget)) := by
  let D : POMProfiniteCylinderCapacityData :=
    { groupCard := groupCard
      lambdaValue := lambdaValue
      epsilon := epsilonGap
      delta := deltaCheb
      n := pom_sync_subtracted_chebotarev_capacity_n_eff ambiguityShell n syncDelay syncTailBudget
      hcard := hcard
      hlambda := hlambda
      hdelta := hdelta
      relativeErrorBound := hRelativeError }
  have hcapacity :
      Real.log (groupCard : ℝ) ≤
        pom_sync_subtracted_chebotarev_capacity_budget lambdaValue epsilonGap deltaCheb
          (pom_sync_subtracted_chebotarev_capacity_n_eff ambiguityShell n syncDelay syncTailBudget) := by
    simpa [D, pom_sync_subtracted_chebotarev_capacity_budget,
      pom_sync_subtracted_chebotarev_capacity_n_eff, POMProfiniteCylinderCapacityData.capacityBudget]
      using paper_pom_profinite_cylinder_capacity D
  refine ⟨hcapacity, ?_, ?_⟩
  · intro hempty
    simpa [pom_sync_subtracted_chebotarev_capacity_budget,
      pom_sync_subtracted_chebotarev_capacity_n_eff,
      pom_sync_subtracted_chebotarev_capacity_n_sync, hempty] using hcapacity
  · intro hnonempty
    simpa [pom_sync_subtracted_chebotarev_capacity_budget,
      pom_sync_subtracted_chebotarev_capacity_n_eff,
      pom_sync_subtracted_chebotarev_capacity_n_sync, hnonempty] using hcapacity

end Omega.POM
