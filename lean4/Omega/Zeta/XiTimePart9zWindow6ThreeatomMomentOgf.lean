import Mathlib.Tactic

namespace Omega.Zeta

/-- The characteristic polynomial `(X - 2)(X - 3)(X - 4)` annihilates each
geometric component of the three-atom moment sequence. -/
lemma xi_time_part9z_window6_threeatom_moment_ogf_geometric_identity (x : Int)
    (hx : x = 2 ∨ x = 3 ∨ x = 4) (n : Nat) :
    x ^ (n + 3) = 9 * x ^ (n + 2) - 26 * x ^ (n + 1) + 24 * x ^ n := by
  rcases hx with rfl | rfl | rfl <;>
    rw [pow_add, pow_add, pow_add] <;>
    ring

/-- Paper label: `thm:xi-time-part9z-window6-threeatom-moment-ogf`. -/
theorem paper_xi_time_part9z_window6_threeatom_moment_ogf (n : Nat) :
    (8 : Int) * 2 ^ (n + 3) + 4 * 3 ^ (n + 3) + 9 * 4 ^ (n + 3) =
      9 * ((8 : Int) * 2 ^ (n + 2) + 4 * 3 ^ (n + 2) + 9 * 4 ^ (n + 2)) -
        26 * ((8 : Int) * 2 ^ (n + 1) + 4 * 3 ^ (n + 1) + 9 * 4 ^ (n + 1)) +
          24 * ((8 : Int) * 2 ^ n + 4 * 3 ^ n + 9 * 4 ^ n) := by
  rw [xi_time_part9z_window6_threeatom_moment_ogf_geometric_identity 2 (Or.inl rfl) n,
    xi_time_part9z_window6_threeatom_moment_ogf_geometric_identity 3 (Or.inr (Or.inl rfl)) n,
    xi_time_part9z_window6_threeatom_moment_ogf_geometric_identity 4 (Or.inr (Or.inr rfl)) n]
  ring

end Omega.Zeta
