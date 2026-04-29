import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDihedralD4QuadraticSubfields

namespace Omega.Zeta

/-- The scaled Ferrari factor corresponding to the `+` sign. -/
def xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled
    (z s lam : ℤ) : ℤ :=
  2 * s * lam ^ 2 - (s + (z + 2)) * lam + s * (z + s)

/-- The scaled Ferrari factor corresponding to the `-` sign. -/
def xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled
    (z s lam : ℤ) : ℤ :=
  2 * s * lam ^ 2 - (s - (z + 2)) * lam + s * (z - s)

lemma xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_scaled_factorization
    (z y s lam : ℤ)
    (hs :
      s ^ 2 = xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y)
    (hcurve : xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y = 0) :
    xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled z s lam *
        xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled z s lam =
      4 * s ^ 2 * xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic y lam := by
  have hfactor :
      xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled z s lam *
          xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled z s lam =
        4 * s ^ 2 * xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic y lam +
          lam ^ 2 *
            (s ^ 2 * (8 * y + 5 + 4 * z) - (z + 2) ^ 2) := by
    have hs0 : s ^ 2 + 4 * y ^ 2 + 4 * y - z ^ 2 = 0 := by
      unfold xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand at hs
      nlinarith
    have hsub :
        xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled z s lam *
            xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled z s lam -
          (4 * s ^ 2 * xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic y lam +
              lam ^ 2 * (s ^ 2 * (8 * y + 5 + 4 * z) - (z + 2) ^ 2)) =
          -s ^ 2 * (s ^ 2 + 4 * y ^ 2 + 4 * y - z ^ 2) := by
      unfold xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled
        xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled
        xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic
      ring
    have hzero : -s ^ 2 * (s ^ 2 + 4 * y ^ 2 + 4 * y - z ^ 2) = 0 := by
      rw [hs0]
      ring
    linarith
  have hlock :
      xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y * (8 * y + 5 + 4 * z) =
        (z + 2) ^ 2 :=
    xi_terminal_zm_dihedral_d4_quadratic_subfields_single_quadratic_closure z y hcurve
  have hsame : s ^ 2 * (8 * y + 5 + 4 * z) = (z + 2) ^ 2 := by
    simpa [hs] using hlock
  rw [hfactor, hsame]
  ring

/-- Paper label: `cor:xi-terminal-zm-dihedral-ferrari-single-quadratic-closure`. On the resolvent
curve, the double-discriminant lock identifies the second Ferrari square root with the same
quadratic radicand `z² - 4y(y+1)`, and the quartic admits the corresponding explicit scaled
quadratic-factor product. -/
theorem paper_xi_terminal_zm_dihedral_ferrari_single_quadratic_closure
    (z y : Int)
    (hcurve : xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y = 0) :
    xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y * (8 * y + 5 + 4 * z) =
        (z + 2) ^ 2 ∧
      (∀ s : Int,
        s ^ 2 = xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y →
          s ^ 2 * (8 * y + 5 + 4 * z) = (z + 2) ^ 2) ∧
      ∀ s lam : Int,
        s ^ 2 = xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y →
          xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qplus_scaled z s lam *
              xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_qminus_scaled z s lam =
            4 * s ^ 2 * xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic y lam := by
  have hlock :
      xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y * (8 * y + 5 + 4 * z) =
        (z + 2) ^ 2 :=
    xi_terminal_zm_dihedral_d4_quadratic_subfields_single_quadratic_closure z y hcurve
  refine ⟨hlock, ?_, ?_⟩
  · intro s hs
    simpa [hs] using hlock
  · intro s lam hs
    exact xi_terminal_zm_dihedral_ferrari_single_quadratic_closure_scaled_factorization
      z y s lam hs hcurve

end Omega.Zeta
