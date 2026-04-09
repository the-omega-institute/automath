import Mathlib.Tactic

namespace Omega.GU.LeyangHolographicN2

variable {K : Type*} [Field K]

/-- Joukowsky map `J_r z = r·z + r⁻¹·z⁻¹`.
    cor:group-jg-leyang-holographic-identity -/
noncomputable def J_r (r z : K) : K := r * z + r⁻¹ * z⁻¹

/-- Degree-2 polynomial factor `P(z) = (z - z₁)(z - z₂)`.
    cor:group-jg-leyang-holographic-identity -/
def P (z z₁ z₂ : K) : K := (z - z₁) * (z - z₂)

/-- Holographic evaluation `r² · P(z) · P((r²z)⁻¹)`.
    cor:group-jg-leyang-holographic-identity -/
noncomputable def Q_r_eval_at_J (r z z₁ z₂ : K) : K :=
  r^2 * P z z₁ z₂ * P ((r^2)⁻¹ * z⁻¹) z₁ z₂

/-- Joukowsky closed form: `J_r(z) = (r²z² + 1)/(rz)`.
    cor:group-jg-leyang-holographic-identity -/
theorem J_r_eq (r z : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    J_r r z = (r^2 * z^2 + 1) / (r * z) := by
  unfold J_r
  field_simp

/-- `P((r²z)⁻¹) = ((1 - z₁·r²·z)(1 - z₂·r²·z)) / (r²z)².
    cor:group-jg-leyang-holographic-identity -/
theorem P_at_reciprocal (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    P ((r^2)⁻¹ * z⁻¹) z₁ z₂ =
      (1 - z₁ * r^2 * z) * (1 - z₂ * r^2 * z) / (r^2 * z)^2 := by
  unfold P
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- `r² · P(z) · P((r²z)⁻¹) = ((z-z₁)(z-z₂)(1-z₁r²z)(1-z₂r²z)) / (r²z²)`.
    cor:group-jg-leyang-holographic-identity -/
theorem r_sq_P_P_reciprocal (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    r^2 * P z z₁ z₂ * P ((r^2)⁻¹ * z⁻¹) z₁ z₂ =
      ((z - z₁) * (z - z₂) * (1 - z₁*r^2*z) * (1 - z₂*r^2*z)) / (r^2 * z^2) := by
  unfold P
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

/-- Unfolding identity.
    cor:group-jg-leyang-holographic-identity -/
theorem Q_r_eval_at_J_eq (r z z₁ z₂ : K) :
    Q_r_eval_at_J r z z₁ z₂ = r^2 * P z z₁ z₂ * P ((r^2)⁻¹ * z⁻¹) z₁ z₂ := rfl

/-- Lee-Yang holographic identity (n=2).
    cor:group-jg-leyang-holographic-identity -/
theorem leyang_holographic_n2 (r z z₁ z₂ : K) :
    Q_r_eval_at_J r z z₁ z₂ =
      r^2 * ((z - z₁) * (z - z₂)) * P ((r^2)⁻¹ * z⁻¹) z₁ z₂ := by
  unfold Q_r_eval_at_J P
  ring

/-- Clearing denominators: `Q · (r²z²) = (z-z₁)(z-z₂)(1-z₁r²z)(1-z₂r²z)`.
    cor:group-jg-leyang-holographic-identity -/
theorem paper_group_jg_leyang_holographic_identity_n2
    (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    Q_r_eval_at_J r z z₁ z₂ * (r^2 * z^2) =
      (z - z₁) * (z - z₂) * (1 - z₁*r^2*z) * (1 - z₂*r^2*z) := by
  unfold Q_r_eval_at_J P
  have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr
  field_simp

end Omega.GU.LeyangHolographicN2
