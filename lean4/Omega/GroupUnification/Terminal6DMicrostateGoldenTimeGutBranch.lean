import Mathlib.Tactic
import Omega.GU.ZeckendorfCountClosure
import Omega.GroupUnification.TerminalFamilyUpliftLock

namespace Omega.GroupUnification

/-- Cross-chapter synthesis of the terminal window-6 tail branch and the three-family uplift lock.
    thm:terminal-6d-microstate-golden-time-gut-branch -/
theorem paper_terminal_6d_microstate_golden_time_gut_branch :
    ({Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset Nat) = ({21, 34, 55} : Finset Nat) ∧
      24 = Nat.fib 8 + Nat.fib 4 ∧
      45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
      78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3 ∧
      15 * 3 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 := by
  rcases Omega.GU.paper_terminal_window6_tail_three_branch with
    ⟨hTail, h24, h45, h78, _, _, _⟩
  rcases paper_terminal_family_uplift_lock with ⟨_, hLock, _⟩
  exact ⟨hTail, h24, h45, h78, hLock⟩

end Omega.GroupUnification
