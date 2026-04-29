import Mathlib.Tactic

namespace Omega.Zeta

/-- The real-coordinate denominator in the Cayley transform
`x ↦ (x - i) / (x + i)`. -/
def xi_rh_cayley_hyperbolicity_cayley_denom (x : ℝ) : ℝ :=
  x ^ 2 + 1

/-- Real part of `(x - i) / (x + i)`, after clearing the complex denominator. -/
noncomputable def xi_rh_cayley_hyperbolicity_cayley_re (x : ℝ) : ℝ :=
  (x ^ 2 - 1) / xi_rh_cayley_hyperbolicity_cayley_denom x

/-- Imaginary part of `(x - i) / (x + i)`, after clearing the complex denominator. -/
noncomputable def xi_rh_cayley_hyperbolicity_cayley_im (x : ℝ) : ℝ :=
  (-2 * x) / xi_rh_cayley_hyperbolicity_cayley_denom x

/-- The real-coordinate Cayley transform into the unit circle. -/
noncomputable def xi_rh_cayley_hyperbolicity_cayley (x : ℝ) : ℝ × ℝ :=
  (xi_rh_cayley_hyperbolicity_cayley_re x,
    xi_rh_cayley_hyperbolicity_cayley_im x)

/-- The projective point at infinity maps to `1` on the unit circle. -/
def xi_rh_cayley_hyperbolicity_cayley_infty : ℝ × ℝ :=
  (1, 0)

/-- Unit-circle predicate in real coordinates. -/
def xi_rh_cayley_hyperbolicity_on_unit_circle (z : ℝ × ℝ) : Prop :=
  z.1 ^ 2 + z.2 ^ 2 = 1

lemma xi_rh_cayley_hyperbolicity_cayley_denom_ne_zero (x : ℝ) :
    xi_rh_cayley_hyperbolicity_cayley_denom x ≠ 0 := by
  unfold xi_rh_cayley_hyperbolicity_cayley_denom
  nlinarith [sq_nonneg x]

lemma xi_rh_cayley_hyperbolicity_cayley_unit (x : ℝ) :
    xi_rh_cayley_hyperbolicity_on_unit_circle
      (xi_rh_cayley_hyperbolicity_cayley x) := by
  unfold xi_rh_cayley_hyperbolicity_on_unit_circle
    xi_rh_cayley_hyperbolicity_cayley xi_rh_cayley_hyperbolicity_cayley_re
    xi_rh_cayley_hyperbolicity_cayley_im
  have hden : xi_rh_cayley_hyperbolicity_cayley_denom x ≠ 0 :=
    xi_rh_cayley_hyperbolicity_cayley_denom_ne_zero x
  unfold xi_rh_cayley_hyperbolicity_cayley_denom at hden ⊢
  field_simp [hden]
  ring

lemma xi_rh_cayley_hyperbolicity_cayley_infty_unit :
    xi_rh_cayley_hyperbolicity_on_unit_circle
      xi_rh_cayley_hyperbolicity_cayley_infty := by
  simp [xi_rh_cayley_hyperbolicity_on_unit_circle,
    xi_rh_cayley_hyperbolicity_cayley_infty]

/-- Concrete Cayley-hyperbolicity interface: the affine real line maps to the unit circle, the
projective point at infinity maps to the unit point, and clearing denominators is legitimate. -/
def xi_rh_cayley_hyperbolicity_statement : Prop :=
  (∀ x : ℝ,
    xi_rh_cayley_hyperbolicity_on_unit_circle
      (xi_rh_cayley_hyperbolicity_cayley x)) ∧
  xi_rh_cayley_hyperbolicity_on_unit_circle
    xi_rh_cayley_hyperbolicity_cayley_infty ∧
  (∀ x : ℝ, xi_rh_cayley_hyperbolicity_cayley_denom x ≠ 0)

/-- Paper label: `prop:xi-rh-cayley-hyperbolicity`. -/
theorem paper_xi_rh_cayley_hyperbolicity : xi_rh_cayley_hyperbolicity_statement := by
  exact ⟨xi_rh_cayley_hyperbolicity_cayley_unit,
    xi_rh_cayley_hyperbolicity_cayley_infty_unit,
    xi_rh_cayley_hyperbolicity_cayley_denom_ne_zero⟩

end Omega.Zeta
