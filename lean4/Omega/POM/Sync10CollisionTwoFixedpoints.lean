import Mathlib.Tactic
import Omega.EA.Sync10UniformInputOutput

namespace Omega.POM

open Omega.EA

/-- Diagonal `q`-tuple in the synchronized `Sync10` product. -/
def sync10DiagonalTuple (q : ℕ) (s : Sync10State) : Fin q → Sync10State :=
  fun _ => s

/-- Output-consistency condition for a one-step synchronized move. -/
def sync10OutputConsistent {q : ℕ} (qs : Fin q → Sync10State) (d : Fin 3) : Prop :=
  ∀ i j, sync10OutputBit (qs i) d = sync10OutputBit (qs j) d

/-- A one-step synchronized loop in the `q`-fold product. -/
def sync10SynchronizedSelfLoop {q : ℕ} (qs : Fin q → Sync10State) (d : Fin 3) : Prop :=
  (∀ i, sync10Step (qs i) d = qs i) ∧ sync10OutputConsistent qs d

lemma sync10_self_loop_iff (s : Sync10State) (d : Fin 3) :
    sync10Step s d = s ↔ (s = .q000 ∧ d = 0) ∨ (s = .q101 ∧ d = 2) := by
  cases s <;> fin_cases d <;> simp [sync10Step]

/-- The only one-step synchronized loops in the positive-length `q`-fold `Sync10` product are the
two diagonal fixed points coming from `q000` with input `0` and `q101` with input `2`. -/
theorem paper_pom_sync10_collision_two_fixedpoints (q : ℕ) (hq : 0 < q)
    (qs : Fin q → Sync10State) (d : Fin 3) :
    sync10SynchronizedSelfLoop qs d ↔
      (qs = sync10DiagonalTuple q Sync10State.q000 ∧ d = 0) ∨
      (qs = sync10DiagonalTuple q Sync10State.q101 ∧ d = 2) := by
  constructor
  · intro h
    let i0 : Fin q := ⟨0, hq⟩
    have h0 := h.1 i0
    rw [sync10_self_loop_iff] at h0
    rcases h0 with h0 | h0
    · left
      rcases h0 with ⟨_, hd0⟩
      refine ⟨?_, hd0⟩
      funext i
      have hi := h.1 i
      rw [hd0, sync10_self_loop_iff] at hi
      rcases hi with hi | hi
      · exact hi.1
      · cases hi.2
    · right
      rcases h0 with ⟨_, hd2⟩
      refine ⟨?_, hd2⟩
      funext i
      have hi := h.1 i
      rw [hd2, sync10_self_loop_iff] at hi
      rcases hi with hi | hi
      · cases hi.2
      · exact hi.1
  · intro h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      refine ⟨?_, ?_⟩
      · intro i
        simp [sync10DiagonalTuple, sync10Step]
      · intro i j
        simp [sync10DiagonalTuple, sync10OutputBit]
    · rcases h with ⟨rfl, rfl⟩
      refine ⟨?_, ?_⟩
      · intro i
        simp [sync10DiagonalTuple, sync10Step]
      · intro i j
        simp [sync10DiagonalTuple, sync10OutputBit]

end Omega.POM
