import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9g-affine-fixed-point-contraction-rigidity`. -/
theorem paper_xi_time_part9g_affine_fixed_point_contraction_rigidity {R : Type*}
    [CommRing R] (B xg x : R) (k n : Nat) :
    ((fun y : R => xg + B ^ k * (y - xg))^[n]) x - xg =
      B ^ (k * n) * (x - xg) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        xg + B ^ k * (((fun y : R => xg + B ^ k * (y - xg))^[n]) x - xg) - xg =
            B ^ k * (((fun y : R => xg + B ^ k * (y - xg))^[n]) x - xg) := by
          ring
        _ = B ^ k * (B ^ (k * n) * (x - xg)) := by
          rw [ih]
        _ = B ^ (k * Nat.succ n) * (x - xg) := by
          simp [Nat.mul_succ, pow_add, mul_assoc, mul_comm]

end Omega.Zeta
