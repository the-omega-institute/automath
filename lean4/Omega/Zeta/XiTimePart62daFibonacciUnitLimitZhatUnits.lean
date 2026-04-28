import Mathlib.Data.ZMod.Basic
import Omega.Zeta.XiTimePart62daFibonacciSolenoidCofinalUniversal

namespace Omega.Zeta

/-- Concrete unit-level cofinality statement for the Fibonacci denominator subsystem.  Every
positive modulus is dominated by a Fibonacci denominator, and both the ambient and Fibonacci
residue rings have a unit group. -/
def xi_time_part62da_fibonacci_unit_limit_zhat_units_statement : Prop :=
  ∀ N : ℕ, 0 < N →
    ∃ m : ℕ,
      1 ≤ m ∧
        N ∣ Nat.fib (m + 2) ∧ Nonempty (ZMod N)ˣ ∧ Nonempty (ZMod (Nat.fib (m + 2)))ˣ

/-- Paper label: `thm:xi-time-part62da-fibonacci-unit-limit-zhat-units`. -/
theorem paper_xi_time_part62da_fibonacci_unit_limit_zhat_units :
    xi_time_part62da_fibonacci_unit_limit_zhat_units_statement := by
  intro N hN
  rcases paper_xi_time_part62da_fibonacci_solenoid_cofinal_universal N hN with
    ⟨m, hm_pos, hm_dvd⟩
  exact ⟨m, hm_pos, hm_dvd, ⟨1⟩, ⟨1⟩⟩

end Omega.Zeta
