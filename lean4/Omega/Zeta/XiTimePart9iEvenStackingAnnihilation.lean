import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_time_part9i_even_stacking_annihilation_even_nsmul {H : Type} [AddCommGroup H]
    (omega : H) (homega : 2 • omega = 0) (k : Nat) : (2 * k) • omega = 0 := by
  rw [mul_nsmul, homega, nsmul_zero]

lemma xi_time_part9i_even_stacking_annihilation_odd_nsmul {H : Type} [AddCommGroup H]
    (omega : H) (homega : 2 • omega = 0) (k : Nat) : (2 * k + 1) • omega = omega := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show 2 * Nat.succ k + 1 = 2 + (2 * k + 1) by omega]
      rw [add_nsmul, homega, ih, zero_add]

/-- Paper label: `cor:xi-time-part9i-even-stacking-annihilation`. -/
theorem paper_xi_time_part9i_even_stacking_annihilation {H : Type} [AddCommGroup H]
    (omega : H) (homega : 2 • omega = 0) :
    (∀ r : Nat, (∃ k : Nat, r = 2 * k) -> r • omega = 0) ∧
      (∀ r : Nat, (∃ k : Nat, r = 2 * k + 1) -> r • omega = omega) := by
  constructor
  · intro r hr
    rcases hr with ⟨k, rfl⟩
    exact xi_time_part9i_even_stacking_annihilation_even_nsmul omega homega k
  · intro r hr
    rcases hr with ⟨k, rfl⟩
    exact xi_time_part9i_even_stacking_annihilation_odd_nsmul omega homega k

end Omega.Zeta
