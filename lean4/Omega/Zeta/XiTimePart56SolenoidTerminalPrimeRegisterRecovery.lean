import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part56-solenoid-terminal-prime-register-recovery`. -/
theorem paper_xi_time_part56_solenoid_terminal_prime_register_recovery
    (S : Finset ℕ) (pComponentNontrivial : ℕ → Prop) :
    (∀ p, p ∈ S ↔ pComponentNontrivial p) → ∀ p, pComponentNontrivial p ↔ p ∈ S := by
  intro h p
  exact (h p).symm

end Omega.Zeta
