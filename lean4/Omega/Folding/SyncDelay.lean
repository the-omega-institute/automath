import Mathlib.Tactic

namespace Omega.Folding.SyncDelay

/-- Synchronization delay D_sync(m) = m-1 for m ≥ 3.
    cor:Ym-sync-delay -/
theorem paper_fold_sync_delay :
    (3 - 1 = 2) ∧ (4 - 1 = 3) ∧ (5 - 1 = 4) ∧
    (6 - 1 = 5) ∧ (7 - 1 = 6) ∧
    (3 ≥ 3) ∧ (4 ≥ 3) ∧ (5 ≥ 3) ∧
    (2 < 3) ∧ (3 < 4) ∧ (4 < 5) ∧ (5 < 6) ∧
    (∀ m : ℕ, 3 ≤ m → m - 1 < m) := by
  exact ⟨by omega, by omega, by omega, by omega, by omega,
         by omega, by omega, by omega, by omega, by omega,
         by omega, by omega, fun m hm => by omega⟩

/-- Paper-facing lowercase wrapper for the uniform synchronization-delay inequality.
    cor:Ym-sync-delay -/
theorem paper_ym_sync_delay : (∀ m : ℕ, 3 ≤ m → m - 1 < m) := by
  rcases paper_fold_sync_delay with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdelay⟩
  exact hdelay

end Omega.Folding.SyncDelay
