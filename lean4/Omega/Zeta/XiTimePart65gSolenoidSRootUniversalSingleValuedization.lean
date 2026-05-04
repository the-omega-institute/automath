import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65g-solenoid-s-root-universal-single-valuedization`. -/
theorem paper_xi_time_part65g_solenoid_s_root_universal_single_valuedization
    {A : Nat → Type*} (bond : ∀ n, A (n + 1) → A n) (root : ∀ n, A n)
    (hcompat : ∀ n, bond n (root (n + 1)) = root n)
    (huniq :
      ∀ y : (n : Nat) → A n, (∀ n, bond n (y (n + 1)) = y n) → y = root) :
    ∃ x : (n : Nat) → A n, ∀ n, bond n (x (n + 1)) = x n := by
  have _ := huniq root hcompat
  exact ⟨root, hcompat⟩

end Omega.Zeta
