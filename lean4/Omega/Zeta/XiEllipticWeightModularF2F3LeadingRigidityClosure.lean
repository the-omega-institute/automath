import Mathlib.Tactic

namespace Omega.Zeta

/-- The quartic certificate for the doubled elliptic-weight image. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P2 (X Y : ℤ) : ℤ :=
  Y ^ 4 - 4 * X ^ 2 * Y ^ 3 + 6 * X ^ 4 * Y ^ 2 - 4 * X ^ 6 * Y + X ^ 8

/-- The quartic certificate for the tripled elliptic-weight image. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P3 (X Y : ℤ) : ℤ :=
  Y ^ 4 - 4 * X ^ 3 * Y ^ 3 + 6 * X ^ 6 * Y ^ 2 - 4 * X ^ 9 * Y + X ^ 12

/-- The doubled torsion-image leading coordinate in the concrete rank-one chart. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage2
    (X : ℤ) : ℤ :=
  X ^ 2

/-- The tripled torsion-image leading coordinate in the concrete rank-one chart. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage3
    (X : ℤ) : ℤ :=
  X ^ 3

/-- The leading coefficient of each quartic modular certificate. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_leadingCoeff : ℤ :=
  1

/-- Concrete paper-facing statement for the F2/F3 leading-rigidity closure certificate. -/
def xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_statement : Prop :=
  (∀ X Y : ℤ,
    xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P2 X Y = (Y - X ^ 2) ^ 4 ∧
      xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P3 X Y = (Y - X ^ 3) ^ 4) ∧
    (∀ X : ℤ,
      xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P2 X
          (xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage2 X) = 0 ∧
        xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P3 X
          (xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage3 X) = 0) ∧
      xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_leadingCoeff = 1

/-- Paper label: `thm:xi-elliptic-weight-modular-f2f3-leading-rigidity-closure`. -/
theorem paper_xi_elliptic_weight_modular_f2f3_leading_rigidity_closure :
    xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_statement := by
  refine ⟨?_, ?_, rfl⟩
  · intro X Y
    constructor <;>
      simp [xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P2,
        xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P3] <;>
      ring
  · intro X
    constructor <;>
      simp [xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P2,
        xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_P3,
        xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage2,
        xi_elliptic_weight_modular_f2f3_leading_rigidity_closure_torsionImage3] <;>
      ring

end Omega.Zeta
