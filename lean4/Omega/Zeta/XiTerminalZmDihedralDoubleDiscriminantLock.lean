import Mathlib.Tactic

namespace Omega.Zeta

/-- The affine resolvent cubic `𝓡(z,y)` from the dihedral specialization package. -/
def xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve (z y : ℤ) : ℤ :=
  z ^ 3 + z ^ 2 - z - 1 + 2 * y * z ^ 2 - 4 * y * z - 5 * y - 4 * y ^ 2 * z - 13 * y ^ 2 -
    8 * y ^ 3

/-- The left-hand side of the double-discriminant lock identity. -/
def xi_terminal_zm_dihedral_double_discriminant_lock_left (z y : ℤ) : ℤ :=
  (z ^ 2 - 4 * y * (y + 1)) * (8 * y + 5 + 4 * z)

/-- The right-hand side of the double-discriminant lock identity. -/
def xi_terminal_zm_dihedral_double_discriminant_lock_right (z : ℤ) : ℤ :=
  (z + 2) ^ 2

/-- Paper label: `prop:xi-terminal-zm-dihedral-double-discriminant-lock`. Expanding the
double-discriminant difference gives exactly `4 * 𝓡(z,y)`, so the lock identity holds on the
resolvent curve `𝓡(z,y) = 0`. -/
theorem paper_xi_terminal_zm_dihedral_double_discriminant_lock (z y : ℤ) :
    (xi_terminal_zm_dihedral_double_discriminant_lock_left z y -
        xi_terminal_zm_dihedral_double_discriminant_lock_right z =
      4 * xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y) ∧
      (xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y = 0 →
        xi_terminal_zm_dihedral_double_discriminant_lock_left z y =
          xi_terminal_zm_dihedral_double_discriminant_lock_right z) := by
  refine ⟨?_, ?_⟩
  · unfold xi_terminal_zm_dihedral_double_discriminant_lock_left
    unfold xi_terminal_zm_dihedral_double_discriminant_lock_right
    unfold xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve
    ring
  · intro hcurve
    have hpoly :
        xi_terminal_zm_dihedral_double_discriminant_lock_left z y -
            xi_terminal_zm_dihedral_double_discriminant_lock_right z =
          4 * xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y := by
      unfold xi_terminal_zm_dihedral_double_discriminant_lock_left
      unfold xi_terminal_zm_dihedral_double_discriminant_lock_right
      unfold xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve
      ring
    rw [hcurve] at hpoly
    linarith

end Omega.Zeta
