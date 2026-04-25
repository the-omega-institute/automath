import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.POM.Sync10CollisionTwoFixedpoints

namespace Omega.POM

open Omega.EA

instance pom_sync10_collision_trace_two_instDecidableSync10SynchronizedSelfLoop {q : ℕ}
    (qs : Fin q → Sync10State) (d : Fin 3) : Decidable (sync10SynchronizedSelfLoop qs d) := by
  unfold sync10SynchronizedSelfLoop sync10OutputConsistent
  infer_instance

theorem paper_pom_sync10_collision_trace_two (q : ℕ) (hq : 0 < q) :
    Fintype.card { p : (Fin q → Sync10State) × Fin 3 // sync10SynchronizedSelfLoop p.1 p.2 } = 2 := by
  classical
  let p0 : (Fin q → Sync10State) × Fin 3 := (sync10DiagonalTuple q Sync10State.q000, 0)
  let p2 : (Fin q → Sync10State) × Fin 3 := (sync10DiagonalTuple q Sync10State.q101, 2)
  let S : Finset ((Fin q → Sync10State) × Fin 3) := {p0, p2}
  have hmem :
      ∀ p : (Fin q → Sync10State) × Fin 3, p ∈ S ↔ sync10SynchronizedSelfLoop p.1 p.2 := by
    intro p
    constructor
    · intro hp
      have hp' :
          (p.1 = sync10DiagonalTuple q Sync10State.q000 ∧ p.2 = 0) ∨
            (p.1 = sync10DiagonalTuple q Sync10State.q101 ∧ p.2 = 2) := by
        rcases (by simpa [S, p0, p2] using hp : p = p0 ∨ p = p2) with hp0 | hp2
        · left
          cases hp0
          exact ⟨rfl, rfl⟩
        · right
          cases hp2
          exact ⟨rfl, rfl⟩
      exact (paper_pom_sync10_collision_two_fixedpoints q hq p.1 p.2).2 hp'
    · intro hp
      have hp' := (paper_pom_sync10_collision_two_fixedpoints q hq p.1 p.2).1 hp
      rcases hp' with hp0 | hp2
      · rcases hp0 with ⟨hqs, hd⟩
        have hpeq : p = p0 := by
          cases p
          simp at hqs hd
          simp [p0, hqs, hd]
        simpa [S, p0, p2] using Or.inl hpeq
      · rcases hp2 with ⟨hqs, hd⟩
        have hpeq : p = p2 := by
          cases p
          simp at hqs hd
          simp [p2, hqs, hd]
        simpa [S, p0, p2] using Or.inr hpeq
  rw [Fintype.card_of_subtype S]
  · simp [S, p0, p2]
  · intro p
    simpa using hmem p

end Omega.POM
