import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-local-binary-normalization-fibonacci-rigidity`. The local
normalization recurrence with the seeds `w 1 = 1` and `w 2 = 2` forces the entire integer-valued
sequence to agree with the shifted Fibonacci numbers. -/
theorem paper_xi_local_binary_normalization_fibonacci_rigidity (w : ℕ → ℤ)
    (hstep : ∀ k, w (k + 2) = w (k + 1) + w k) (h1 : w 1 = 1) (h2 : w 2 = 2) :
    ∀ k, w k = Int.ofNat (Nat.fib (k + 1)) := by
  have hw0 : w 0 = 1 := by
    have h0 : (2 : ℤ) = 1 + w 0 := by simpa [h1, h2] using hstep 0
    linarith
  have hpair : ∀ n, w n = Int.ofNat (Nat.fib (n + 1)) ∧ w (n + 1) = Int.ofNat (Nat.fib (n + 2)) := by
    intro n
    induction n with
    | zero =>
        exact ⟨by simpa using hw0, by simpa using h1⟩
    | succ n ihn =>
        rcases ihn with ⟨ihn0, ihn1⟩
        refine ⟨by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ihn1, ?_⟩
        have hrec : w (n + 2) = w (n + 1) + w n := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep n
        have hfib :
            Int.ofNat (Nat.fib (n + 3)) =
              Int.ofNat (Nat.fib (n + 1)) + Int.ofNat (Nat.fib (n + 2)) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            congrArg Int.ofNat (Nat.fib_add_two (n := n + 1))
        calc
          w (n + 2) = w (n + 1) + w n := hrec
          _ = Int.ofNat (Nat.fib (n + 2)) + Int.ofNat (Nat.fib (n + 1)) := by rw [ihn1, ihn0]
          _ = Int.ofNat (Nat.fib (n + 1)) + Int.ofNat (Nat.fib (n + 2)) := by rw [add_comm]
          _ = Int.ofNat (Nat.fib (n + 3)) := hfib.symm
  intro k
  exact (hpair k).1

end Omega.Zeta
