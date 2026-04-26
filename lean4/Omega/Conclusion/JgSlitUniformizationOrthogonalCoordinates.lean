import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The real `x`-coordinate of the Joukowsky chart `w = z + z⁻¹` with `z = exp (u + i θ)`. -/
def conclusion_jg_slit_uniformization_orthogonal_coordinates_x (u θ : ℝ) : ℝ :=
  2 * Real.cosh u * Real.cos θ

/-- The real `y`-coordinate of the Joukowsky chart `w = z + z⁻¹` with `z = exp (u + i θ)`. -/
def conclusion_jg_slit_uniformization_orthogonal_coordinates_y (u θ : ℝ) : ℝ :=
  2 * Real.sinh u * Real.sin θ

/-- The `u`-direction derivative of the coordinate chart. -/
def conclusion_jg_slit_uniformization_orthogonal_coordinates_du (u θ : ℝ) : ℝ × ℝ :=
  (2 * Real.sinh u * Real.cos θ, 2 * Real.cosh u * Real.sin θ)

/-- The `θ`-direction derivative of the coordinate chart. -/
def conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta (u θ : ℝ) : ℝ × ℝ :=
  (-2 * Real.cosh u * Real.sin θ, 2 * Real.sinh u * Real.cos θ)

/-- The explicit slit-plane chart written in real coordinates. -/
def conclusion_jg_slit_uniformization_orthogonal_coordinates_w (u θ : ℝ) : ℂ :=
  Complex.mk
    (conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ)
    (conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ)

/-- Paper label: `thm:conclusion-jg-slit-uniformization-orthogonal-coordinates`.
The concrete Joukowsky chart has the displayed ellipse and hyperbola equations, the coordinate
vectors are orthogonal, and both metric coefficients equal the same conformal factor. -/
theorem paper_conclusion_jg_slit_uniformization_orthogonal_coordinates
    (u θ : ℝ) (hu : 0 < u) (hθsin : Real.sin θ ≠ 0) (hθcos : Real.cos θ ≠ 0) :
    conclusion_jg_slit_uniformization_orthogonal_coordinates_w u θ =
      Complex.mk (2 * Real.cosh u * Real.cos θ) (2 * Real.sinh u * Real.sin θ) ∧
      ((conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ) /
          (2 * Real.cosh u)) ^ 2 +
        ((conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ) /
            (2 * Real.sinh u)) ^ 2 = 1 ∧
      ((conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ) /
          (2 * Real.cos θ)) ^ 2 -
        ((conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ) /
            (2 * Real.sin θ)) ^ 2 = 1 ∧
      (conclusion_jg_slit_uniformization_orthogonal_coordinates_du u θ).1 *
          (conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta u θ).1 +
        (conclusion_jg_slit_uniformization_orthogonal_coordinates_du u θ).2 *
          (conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta u θ).2 = 0 ∧
      (conclusion_jg_slit_uniformization_orthogonal_coordinates_du u θ).1 ^ 2 +
          (conclusion_jg_slit_uniformization_orthogonal_coordinates_du u θ).2 ^ 2 =
        4 * (Real.cosh u ^ 2 - Real.cos θ ^ 2) ∧
      (conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta u θ).1 ^ 2 +
          (conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta u θ).2 ^ 2 =
        4 * (Real.cosh u ^ 2 - Real.cos θ ^ 2) := by
  have hsinh_pos : 0 < Real.sinh u := by
    simpa using (Real.sinh_pos_iff.mpr hu)
  have h2cosh_ne : 2 * Real.cosh u ≠ 0 := by
    have hcosh_pos : 0 < Real.cosh u := Real.cosh_pos u
    linarith
  have h2sinh_ne : 2 * Real.sinh u ≠ 0 := by
    linarith
  have h2cos_ne : 2 * Real.cos θ ≠ 0 := by
    intro hzero
    apply hθcos
    linarith
  have h2sin_ne : 2 * Real.sin θ ≠ 0 := by
    intro hzero
    apply hθsin
    linarith
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hhyper : Real.cosh u ^ 2 - Real.sinh u ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq u
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      ((conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ) / (2 * Real.cosh u)) ^ 2 +
            ((conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ) /
                (2 * Real.sinh u)) ^ 2
          = Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
              have hxdiv :
                  conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ /
                      (2 * Real.cosh u) = Real.cos θ := by
                unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_x
                field_simp [h2cosh_ne]
              have hydiv :
                  conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ /
                      (2 * Real.sinh u) = Real.sin θ := by
                unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_y
                field_simp [h2sinh_ne]
              rw [hxdiv, hydiv]
      _ = 1 := htrig
  · calc
      ((conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ) / (2 * Real.cos θ)) ^ 2 -
            ((conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ) /
                (2 * Real.sin θ)) ^ 2
          = Real.cosh u ^ 2 - Real.sinh u ^ 2 := by
              have hxdiv :
                  conclusion_jg_slit_uniformization_orthogonal_coordinates_x u θ /
                      (2 * Real.cos θ) = Real.cosh u := by
                unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_x
                field_simp [h2cos_ne]
              have hydiv :
                  conclusion_jg_slit_uniformization_orthogonal_coordinates_y u θ /
                      (2 * Real.sin θ) = Real.sinh u := by
                unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_y
                field_simp [h2sin_ne]
              rw [hxdiv, hydiv]
      _ = 1 := hhyper
  · unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_du
      conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta
    ring
  · unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_du
    nlinarith [htrig, hhyper]
  · unfold conclusion_jg_slit_uniformization_orthogonal_coordinates_dtheta
    nlinarith [htrig, hhyper]

end

end Omega.Conclusion
