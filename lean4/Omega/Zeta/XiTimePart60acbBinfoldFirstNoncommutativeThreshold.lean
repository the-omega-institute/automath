import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part60acb-binfold-first-noncommutative-threshold`. -/
theorem paper_xi_time_part60acb_binfold_first_noncommutative_threshold
    (Simple Commutative : ℕ → Prop)
    (hSimple : ∀ m, 1 ≤ m → ¬ Simple m)
    (hComm : ∀ m, 1 ≤ m → (Commutative m ↔ 2 ^ m = Nat.fib (m + 2))) :
    (∀ m, 1 ≤ m → ¬ Simple m) ∧
      (∀ m, 1 ≤ m → (Commutative m ↔ m = 1)) ∧ ¬ Commutative 2 := by
  refine ⟨hSimple, ?_, ?_⟩
  · intro m hm
    constructor
    · intro hC
      rcases Nat.eq_or_lt_of_le hm with hm_one | hm_gt_one
      · exact hm_one.symm
      · have hm_two : 2 ≤ m := by omega
        have hEq : 2 ^ m = Nat.fib (m + 2) := (hComm m hm).1 hC
        have hLt : Nat.fib (m + 2) < 2 ^ m :=
          Omega.fib_lt_pow_two_of_ge_two m hm_two
        omega
    · intro hm_one
      subst m
      exact (hComm 1 (by omega)).2 (by native_decide)
  · intro hC
    have hEq : 2 ^ 2 = Nat.fib (2 + 2) := (hComm 2 (by omega)).1 hC
    have hLt : Nat.fib (2 + 2) < 2 ^ 2 :=
      Omega.fib_lt_pow_two_of_ge_two 2 (by omega)
    omega

end Omega.Zeta
