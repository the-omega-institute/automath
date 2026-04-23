import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDihedralDoubleDiscriminantLock
import Omega.Zeta.XiTimePart9gLeyangCubicDiscriminant

namespace Omega.Zeta

/-- The specialized quartic from the dihedral `D₄` discussion. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic (y lam : ℤ) : ℤ :=
  lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1)

/-- The quartic discriminant factors through the explicit cubic from the Lee-Yang audit. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant (y : ℤ) : ℤ :=
  -y * (y - 1) * xiTimePart9gLeyangCubic y

/-- The three transitive subgroups of `D₄` relevant to the quartic specialization. -/
inductive xi_terminal_zm_dihedral_d4_quadratic_subfields_group
  | c4
  | v4
  | d4
  deriving DecidableEq, Repr

/-- The Ferrari quadratic radicand. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand (z y : ℤ) : ℤ :=
  z ^ 2 - 4 * y * (y + 1)

/-- The discriminant quadratic radicand. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand (y : ℤ) : ℤ :=
  xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y

/-- The third quadratic radicand in the `D₄` index-`2` lattice. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_mixed_radicand (z y : ℤ) : ℤ :=
  xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y *
    xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand y

/-- The two visible quadratic generators are distinct, and so is their product field. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct (z y : ℤ) : Prop :=
  xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y ≠
      xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand y ∧
    xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y ≠
      xi_terminal_zm_dihedral_d4_quadratic_subfields_mixed_radicand z y ∧
    xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand y ≠
      xi_terminal_zm_dihedral_d4_quadratic_subfields_mixed_radicand z y

instance xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct_decidable
    (z y : ℤ) :
    Decidable (xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct z y) := by
  unfold xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct
  infer_instance

/-- Audited classification inside the dihedral envelope: square discriminant gives `V₄`; otherwise
two distinct quadratic generators force `D₄`; the remaining case is `C₄`. -/
def xi_terminal_zm_dihedral_d4_quadratic_subfields_predicted_group (z y : ℤ) :
    xi_terminal_zm_dihedral_d4_quadratic_subfields_group :=
  if IsSquare (xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y) then
    .v4
  else if xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct z y then
    .d4
  else
    .c4

lemma xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant_factorization
    (y : ℤ) :
    xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y =
      -y * (y - 1) * xiTimePart9gLeyangCubic y := by
  rfl

lemma xi_terminal_zm_dihedral_d4_quadratic_subfields_single_quadratic_closure
    (z y : ℤ)
    (hcurve : xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y = 0) :
    xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y * (8 * y + 5 + 4 * z) =
      (z + 2) ^ 2 := by
  simpa [xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand,
    xi_terminal_zm_dihedral_double_discriminant_lock_left,
    xi_terminal_zm_dihedral_double_discriminant_lock_right] using
      (paper_xi_terminal_zm_dihedral_double_discriminant_lock z y).2 hcurve

/-- Paper label: `prop:xi-terminal-zm-dihedral-d4-quadratic-subfields`. The resolvent-curve
identity gives the Ferrari single-quadratic closure, the quartic discriminant is the explicit
factor `-y(y-1)(256 y^3 + 411 y^2 + 165 y + 32)`, and a nonsquare discriminant together with two
distinct quadratic generators puts the specialization in the `D₄` branch of the dihedral audit.
-/
theorem paper_xi_terminal_zm_dihedral_d4_quadratic_subfields
    (z y : ℤ)
    (hcurve : xi_terminal_zm_dihedral_double_discriminant_lock_resolventCurve z y = 0)
    (hdisc_nonsquare :
      ¬ IsSquare (xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y))
    (hpairwise : xi_terminal_zm_dihedral_d4_quadratic_subfields_pairwise_distinct z y) :
    xi_terminal_zm_dihedral_d4_quadratic_subfields_predicted_group z y = .d4 ∧
      xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y * (8 * y + 5 + 4 * z) =
        (z + 2) ^ 2 ∧
      xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y =
        -y * (y - 1) * xiTimePart9gLeyangCubic y ∧
      xi_terminal_zm_dihedral_d4_quadratic_subfields_ferrari_radicand z y ≠
        xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand y ∧
      xi_terminal_zm_dihedral_d4_quadratic_subfields_discriminant_radicand y ≠
        xi_terminal_zm_dihedral_d4_quadratic_subfields_mixed_radicand z y := by
  refine ⟨?_, xi_terminal_zm_dihedral_d4_quadratic_subfields_single_quadratic_closure z y hcurve,
    xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant_factorization y, ?_, ?_⟩
  · unfold xi_terminal_zm_dihedral_d4_quadratic_subfields_predicted_group
    by_cases hsq : IsSquare (xi_terminal_zm_dihedral_d4_quadratic_subfields_quartic_discriminant y)
    · exact (hdisc_nonsquare hsq).elim
    · simp [hsq, hpairwise]
  · exact hpairwise.1
  · exact hpairwise.2.2

end Omega.Zeta
