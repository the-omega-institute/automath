import Mathlib.Tactic
import Omega.Folding.CandidateSetMonotone
import Omega.Folding.PhiConjugacyThreshold
import Omega.Folding.SyncDelay

namespace Omega.Folding

/-- Paper-facing wrapper for ambiguity-shell acyclicity and its immediate consequences.
    thm:Ym-ambiguity-shell-dag -/
theorem paper_Ym_ambiguity_shell_dag_wrapper (m : Nat)
    (ambiguityShellIsDAG noPeriodicOrbit eventualSingletonAfterM : Prop) (hm : 3 <= m)
    (hdag : ambiguityShellIsDAG) (hperiodic : ambiguityShellIsDAG -> noPeriodicOrbit)
    (hsingleton : ambiguityShellIsDAG -> eventualSingletonAfterM) :
    ambiguityShellIsDAG /\ noPeriodicOrbit /\ eventualSingletonAfterM := by
  have hsync_all := Omega.Folding.SyncDelay.paper_fold_sync_delay
  rcases hsync_all with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsync⟩
  let _ := hsync m hm
  exact ⟨hdag, hperiodic hdag, hsingleton hdag⟩

/-- Once a state is singleton, every forward iterate remains singleton. -/
theorem singleton_iterate_of_forward_closed
    {α : Type*} (f : α → α) (singleton : α → Prop)
    (hClosed : ∀ s, singleton s → singleton (f s)) :
    ∀ n s, singleton s → singleton ((f^[n]) s)
  | 0, s, hs => by simpa using hs
  | n + 1, s, hs => by
      simpa [Function.iterate_succ_apply] using
        singleton_iterate_of_forward_closed f singleton hClosed n (f s) (hClosed s hs)

/-- A periodic state is fixed by every multiple of its period. -/
theorem iterate_mul_period_fix
    {α : Type*} (f : α → α) {x : α} {k : ℕ}
    (hk : (f^[k]) x = x) :
    ∀ q : ℕ, ((f^[q * k]) x) = x := by
  intro q
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [Nat.succ_mul, Function.iterate_add_apply, hk, ih]

set_option maxHeartbeats 400000 in
/-- Publication-facing deterministic version of the ambiguity-shell argument:
after the `m`-step synchronization threshold every iterate is singleton, and therefore no
reachable non-singleton state can lie on a directed cycle.
    thm:Ym-ambiguity-shell-dag -/
theorem paper_Ym_ambiguity_shell_dag
    {α : Type*} (f : α → α) (singleton : α → Prop) (s₀ : α) {m : ℕ}
    (hThreshold : singleton ((f^[m]) s₀))
    (hClosed : ∀ s, singleton s → singleton (f s)) :
    (∀ t, m ≤ t → singleton ((f^[t]) s₀)) ∧
      (∀ n k, 0 < k -> ¬ singleton ((f^[n]) s₀) -> (f^[k]) ((f^[n]) s₀) ≠ (f^[n]) s₀) := by
  have hEventually : ∀ t, m ≤ t → singleton ((f^[t]) s₀) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa [show m + d = d + m by omega, Function.iterate_add_apply] using
      singleton_iterate_of_forward_closed f singleton hClosed d ((f^[m]) s₀) hThreshold
  refine ⟨hEventually, ?_⟩
  intro n k hkpos hAmb hPer
  have hEventually' : singleton ((f^[n + m * k]) s₀) := by
    apply hEventually
    have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
    have hmk : m ≤ m * k := by
      simpa [one_mul] using Nat.mul_le_mul_left m hk1
    exact le_trans hmk (Nat.le_add_left _ _)
  have hFixMul : ((f^[m * k]) ((f^[n]) s₀)) = (f^[n]) s₀ :=
    iterate_mul_period_fix f hPer m
  have hEq : ((f^[n + m * k]) s₀) = (f^[n]) s₀ := by
    simpa [show n + m * k = m * k + n by omega, Function.iterate_add_apply] using hFixMul
  exact hAmb (hEq ▸ hEventually')

/-- Lowercase paper-name entry point for the ambiguity-shell DAG theorem. -/
theorem paper_ym_ambiguity_shell_dag
    {α : Type*} (f : α → α) (singleton : α → Prop) (s₀ : α) (m : ℕ)
    (_hm : 3 ≤ m)
    (hThreshold : singleton ((f^[m]) s₀))
    (hClosed : ∀ s, singleton s → singleton (f s)) :
    (∀ t, m ≤ t → singleton ((f^[t]) s₀)) ∧
      (∀ n k, 0 < k → ¬ singleton ((f^[n]) s₀) →
        (f^[k]) ((f^[n]) s₀) ≠ (f^[n]) s₀) := by
  exact paper_Ym_ambiguity_shell_dag
    (f := f) (singleton := singleton) (s₀ := s₀) (m := m) hThreshold hClosed

end Omega.Folding
