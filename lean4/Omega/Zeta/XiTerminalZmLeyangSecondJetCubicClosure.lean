import Mathlib.Tactic

namespace Omega.Zeta

/-- The displayed cubic closure relation for the second jet coordinates. -/
def xi_terminal_zm_leyang_second_jet_cubic_closure_relation {R : Type*} [Ring R]
    (y delta delta2 : R) : R :=
  64 * delta ^ 3 + 96 * delta ^ 2 * delta2 + 576 * delta ^ 2 * y -
    288 * delta ^ 2 + 48 * delta * delta2 ^ 2 - 144 * delta * delta2 * y -
    216 * delta * delta2 + 9600 * delta * y ^ 3 - 5424 * delta * y ^ 2 +
    1200 * delta * y + 132 * delta + 8 * delta2 ^ 3 - 216 * delta2 ^ 2 * y -
    63 * delta2 ^ 2 - 3200 * delta2 * y ^ 3 - 1392 * delta2 * y ^ 2 +
    1008 * delta2 * y + 128 * delta2 + 16000 * y ^ 3 - 2640 * y ^ 2 -
    816 * y - 16

/-- Paper label: `thm:xi-terminal-zm-leyang-second-jet-cubic-closure`. -/
theorem paper_xi_terminal_zm_leyang_second_jet_cubic_closure {R : Type*} [Field R]
    (X Y y delta delta2 : R) (hE : Y ^ 2 = X ^ 3 - X + (1 / 4 : R))
    (hy : y = X ^ 2 + Y - (1 / 2 : R))
    (hdelta : delta = 4 * X * Y + 3 * X ^ 2 - 1)
    (hdelta2 : delta2 = 20 * X ^ 3 - 12 * X + 2 + 12 * X * Y) :
    xi_terminal_zm_leyang_second_jet_cubic_closure_relation y delta delta2 = 0 := by
  have xi_terminal_zm_leyang_second_jet_cubic_closure_elliptic_equation := hE
  clear xi_terminal_zm_leyang_second_jet_cubic_closure_elliptic_equation
  subst y
  subst delta
  subst delta2
  unfold xi_terminal_zm_leyang_second_jet_cubic_closure_relation
  by_cases h2 : (2 : R) = 0
  · have h2inv : (2 : R)⁻¹ = 0 := by simp [h2]
    ring_nf
    simp [h2inv]
    linear_combination
      (-(552 : R) * X - 624 * X * Y + 9600 * X * Y ^ 2 - 4122 * X ^ 2 -
          1656 * X ^ 2 * Y + 14400 * X ^ 2 * Y ^ 2 - 3832 * X ^ 3 +
          50640 * X ^ 3 * Y - 48000 * X ^ 3 * Y ^ 2 + 8280 * X ^ 4 +
          14400 * X ^ 4 * Y + 36720 * X ^ 5 - 96000 * X ^ 5 * Y -
          48000 * X ^ 7) * h2
  · field_simp [h2]
    ring_nf

end Omega.Zeta
