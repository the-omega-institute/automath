import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt

namespace Omega.EA.JoukowskyEllipse

/-- Diagonal action `diag(r, r⁻¹) · (x, y) = (r·x, r⁻¹·y)`.
    thm:prime-register-dense-ellipticization -/
noncomputable def diagAction (r x y : ℝ) : ℝ × ℝ := (r * x, r⁻¹ * y)

/-- The diagonal action sends the unit circle to the ellipse with semi-axes `(r, r⁻¹)`.
    thm:prime-register-dense-ellipticization -/
theorem diag_maps_circle_to_ellipse (r x y : ℝ) (hr : r ≠ 0)
    (h : x^2 + y^2 = 1) :
    ((diagAction r x y).1 / r)^2 + ((diagAction r x y).2 * r)^2 = 1 := by
  unfold diagAction
  simp only
  have hx : (r * x) / r = x := by field_simp
  have hy : (r⁻¹ * y) * r = y := by field_simp
  rw [hx, hy]
  exact h

/-- Ellipse axis product equals `1`.
    thm:prime-register-dense-ellipticization -/
theorem ellipse_axes_product (r : ℝ) (hr : r ≠ 0) : r * r⁻¹ = 1 :=
  mul_inv_cancel₀ hr

/-- Axis ratio equals `r²` for `r ≥ 1`.
    thm:prime-register-dense-ellipticization -/
theorem axis_ratio_eq_r_sq (r : ℝ) (hr : 1 ≤ r) : r / r⁻¹ = r^2 := by
  have h0 : r ≠ 0 := by linarith
  field_simp

/-- Positive square root is unique.
    thm:prime-register-dense-ellipticization -/
theorem r_unique_from_sq (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (heq : r₁^2 = r₂^2) : r₁ = r₂ := by
  nlinarith [sq_nonneg (r₁ - r₂), sq_nonneg (r₁ + r₂)]

/-- Ellipse area equals `π` (semi-axis product times `π`).
    thm:prime-register-dense-ellipticization -/
theorem ellipse_area_eq_pi (r : ℝ) (hr : r ≠ 0) :
    Real.pi * r * r⁻¹ = Real.pi := by
  rw [mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- Paper package (part 2): ellipticisation axis/ratio/area identities.
    thm:prime-register-dense-ellipticization -/
theorem paper_prime_register_dense_ellipticization_part2
    (r : ℝ) (hr : 1 ≤ r) :
    r * r⁻¹ = 1 ∧ r / r⁻¹ = r^2 ∧ Real.pi * r * r⁻¹ = Real.pi := by
  have h0 : r ≠ 0 := by linarith
  exact ⟨ellipse_axes_product r h0, axis_ratio_eq_r_sq r hr, ellipse_area_eq_pi r h0⟩

/-- The second radial moment of the normalized Joukowsky ellipse. -/
noncomputable def joukowskySecondRadialMoment (r : ℝ) : ℝ :=
  r ^ 2 + (r⁻¹) ^ 2

/-- The second radial moment determines the branch parameter in the normalized regime `r ≥ 1`. -/
noncomputable def primeRegisterJoukowskyRadialMomentInvert (r : ℝ) : Prop :=
  joukowskySecondRadialMoment r = r ^ 2 + (r⁻¹) ^ 2 ∧
    r = Real.sqrt ((joukowskySecondRadialMoment r +
      Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4)) / 2)

/-- The second radial moment `R₂(r) = r² + r⁻²` inverts to the positive branch `r` under the
normalization `r ≥ 1`.
    prop:prime-register-joukowsky-radial-moment-invert -/
theorem paper_prime_register_joukowsky_radial_moment_invert (r : Real) (hr : 1 <= r) :
    primeRegisterJoukowskyRadialMomentInvert r := by
  have h0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h0ne : r ≠ 0 := ne_of_gt h0
  have hdiff_nonneg : 0 ≤ r ^ 2 - (r⁻¹) ^ 2 := by
    have hr2_ge : 1 ≤ r ^ 2 := by nlinarith
    have hpow : 1 ≤ r ^ 4 := by nlinarith
    have hmul_nonneg : 0 ≤ r ^ 4 - 1 := by linarith
    have hmul :
        r ^ 2 * (r ^ 2 - (r⁻¹) ^ 2) = r ^ 4 - 1 := by
      field_simp [h0ne]
    have : 0 ≤ r ^ 2 * (r ^ 2 - (r⁻¹) ^ 2) := by rw [hmul]; exact hmul_nonneg
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using this) (sq_pos_of_pos h0)
  refine ⟨rfl, ?_⟩
  have hsqr :
      Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4) = r ^ 2 - (r⁻¹) ^ 2 := by
    unfold joukowskySecondRadialMoment
    rw [show (r ^ 2 + (r⁻¹) ^ 2) ^ 2 - 4 = (r ^ 2 - (r⁻¹) ^ 2) ^ 2 by
      field_simp [h0ne]
      ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hdiff_nonneg]
  have hinner :
      (joukowskySecondRadialMoment r + Real.sqrt (joukowskySecondRadialMoment r ^ 2 - 4)) / 2
        = r ^ 2 := by
    have hsqr' : Real.sqrt ((r ^ 2 + (r⁻¹) ^ 2) ^ 2 - 4) = r ^ 2 - (r⁻¹) ^ 2 := by
      simpa [joukowskySecondRadialMoment] using hsqr
    unfold joukowskySecondRadialMoment
    rw [hsqr']
    field_simp
    ring
  rw [hinner, Real.sqrt_sq (show 0 ≤ r by linarith)]

end Omega.EA.JoukowskyEllipse
