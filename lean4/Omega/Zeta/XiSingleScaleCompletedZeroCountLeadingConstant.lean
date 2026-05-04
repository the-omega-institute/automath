import Mathlib.Tactic

universe u v

namespace List

def bind {α : Type u} {β : Type v} (roots : List α) (tower : α → List β) : List β :=
  roots.flatMap tower

end List

namespace Omega.Zeta

/-- Paper label: `prop:xi-single-scale-completed-zero-count-leading-constant`. -/
theorem paper_xi_single_scale_completed_zero_count_leading_constant {α : Type u}
    (roots : List α) (inStrip : α → Bool) (T : Nat) :
    ((roots.filter inStrip).bind (fun _ => List.range (2 * T + 1))).length =
      (roots.filter inStrip).length * (2 * T + 1) := by
  unfold List.bind
  induction roots.filter inStrip with
  | nil =>
      simp
  | cons _ tail _ =>
      simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

end Omega.Zeta
