import Mathlib.Tactic

namespace Omega.Zeta

private theorem xi_time_part62di_max_noncontractible_fiber_sixstep_renormalization_fib_add_six
    (n : ℕ) :
    Nat.fib (n + 6) = 4 * Nat.fib (n + 3) + Nat.fib n := by
  have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have h4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have h5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
  have h6 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
  rw [h6, h5, h4, h3, h2]
  ring

/-- Paper label: `thm:xi-time-part62di-max-noncontractible-fiber-sixstep-renormalization`. -/
theorem paper_xi_time_part62di_max_noncontractible_fiber_sixstep_renormalization :
    (∀ c r : ℕ,
      Nat.fib (3 * (r + 2) + c) =
        4 * Nat.fib (3 * (r + 1) + c) + Nat.fib (3 * r + c)) := by
  intro c r
  have h0 : 3 * (r + 2) + c = 3 * r + c + 6 := by omega
  have h1 : 3 * (r + 1) + c = 3 * r + c + 3 := by omega
  rw [h0, h1]
  exact xi_time_part62di_max_noncontractible_fiber_sixstep_renormalization_fib_add_six
    (3 * r + c)

end Omega.Zeta
