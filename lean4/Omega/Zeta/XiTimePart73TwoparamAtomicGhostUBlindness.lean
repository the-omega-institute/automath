import Mathlib.Tactic

namespace Omega.Zeta

/-- Atomic ghost coefficient coming from the parity split of `(1 - v z^2)^{-1}`. -/
def xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost
    (_u v : Real) (n : Nat) : Real :=
  if n % 2 = 0 then 2 * v ^ (n / 2) else 0

/-- Paper label: `thm:xi-time-part73-twoparam-atomic-ghost-u-blindness`. -/
theorem paper_xi_time_part73_twoparam_atomic_ghost_u_blindness
    (u1 u2 v : Real) (n : Nat) :
    xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost u1 v n =
        xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost u2 v n ∧
      (n % 2 = 1 ->
        xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost u1 v n = 0) := by
  constructor
  · simp [xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost]
  · intro hn
    have hne : n % 2 ≠ 0 := by omega
    simp [xi_time_part73_twoparam_atomic_ghost_u_blindness_atomGhost, hne]

end Omega.Zeta
