import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Coordinate data for a traceless Poisson--Cauchy quadrupole. -/
structure conclusion_poisson_cauchy_tv_second_order_norm_data where
  A : ℝ
  B : ℝ

/-- The even coordinate-axis TV constant. -/
def conclusion_poisson_cauchy_tv_second_order_norm_evenConstant : ℝ :=
  3 * Real.sqrt 3 / (4 * Real.pi)

/-- The odd coordinate-axis TV constant. -/
def conclusion_poisson_cauchy_tv_second_order_norm_oddConstant : ℝ :=
  5 / (2 * Real.pi)

/-- The prefixed linear `L¹` image of the traceless coordinates. -/
def conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image (A B : ℝ) : ℝ × ℝ :=
  (conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * A,
    conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * B)

/-- The two-coordinate `L¹` norm used by the finite TV certificate. -/
def conclusion_poisson_cauchy_tv_second_order_norm_l1Norm (u : ℝ × ℝ) : ℝ :=
  |u.1| + |u.2|

/-- The TV second-order functional induced by the concrete linear `L¹` image. -/
def conclusion_poisson_cauchy_tv_second_order_norm_tv (A B : ℝ) : ℝ :=
  conclusion_poisson_cauchy_tv_second_order_norm_l1Norm
    (conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image A B)

/-- Paper-facing norm statement for one quadrupole coordinate pair, with universal operations
against any second coordinate pair. -/
def conclusion_poisson_cauchy_tv_second_order_norm_statement
    (D : conclusion_poisson_cauchy_tv_second_order_norm_data) : Prop :=
  0 ≤ conclusion_poisson_cauchy_tv_second_order_norm_tv D.A D.B ∧
    (∀ r : ℝ,
      conclusion_poisson_cauchy_tv_second_order_norm_tv (r * D.A) (r * D.B) =
        |r| * conclusion_poisson_cauchy_tv_second_order_norm_tv D.A D.B) ∧
      (∀ E : conclusion_poisson_cauchy_tv_second_order_norm_data,
        conclusion_poisson_cauchy_tv_second_order_norm_tv (D.A + E.A) (D.B + E.B) ≤
          conclusion_poisson_cauchy_tv_second_order_norm_tv D.A D.B +
            conclusion_poisson_cauchy_tv_second_order_norm_tv E.A E.B) ∧
        (conclusion_poisson_cauchy_tv_second_order_norm_tv D.A D.B = 0 ↔
          D.A = 0 ∧ D.B = 0) ∧
          conclusion_poisson_cauchy_tv_second_order_norm_tv D.A 0 =
            conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * |D.A| ∧
            conclusion_poisson_cauchy_tv_second_order_norm_tv 0 D.B =
              conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * |D.B|

/-- Paper label: `thm:conclusion-poisson-cauchy-tv-second-order-norm`. -/
theorem paper_conclusion_poisson_cauchy_tv_second_order_norm
    (D : conclusion_poisson_cauchy_tv_second_order_norm_data) :
    conclusion_poisson_cauchy_tv_second_order_norm_statement D := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_ne : Real.pi ≠ 0 := hpi_pos.ne'
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have heven_pos : 0 < conclusion_poisson_cauchy_tv_second_order_norm_evenConstant := by
    unfold conclusion_poisson_cauchy_tv_second_order_norm_evenConstant
    positivity
  have hodd_pos : 0 < conclusion_poisson_cauchy_tv_second_order_norm_oddConstant := by
    unfold conclusion_poisson_cauchy_tv_second_order_norm_oddConstant
    positivity
  have heven_ne :
      conclusion_poisson_cauchy_tv_second_order_norm_evenConstant ≠ 0 := heven_pos.ne'
  have hodd_ne :
      conclusion_poisson_cauchy_tv_second_order_norm_oddConstant ≠ 0 := hodd_pos.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
      conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
      conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · intro r
    simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
      conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
      conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image, abs_mul,
      mul_left_comm, left_distrib]
  · intro E
    have hA :
        |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * (D.A + E.A)| ≤
          |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * D.A| +
            |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * E.A| := by
      calc
        |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * (D.A + E.A)| =
            |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * D.A +
              conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * E.A| := by
              ring_nf
        _ ≤
            |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * D.A| +
              |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * E.A| :=
              abs_add_le _ _
    have hB :
        |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * (D.B + E.B)| ≤
          |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * D.B| +
            |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * E.B| := by
      calc
        |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * (D.B + E.B)| =
            |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * D.B +
              conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * E.B| := by
              ring_nf
        _ ≤
            |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * D.B| +
              |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * E.B| :=
              abs_add_le _ _
    simp only [abs_mul] at hA hB
    simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
      conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
      conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image]
    linarith
  · constructor
    · intro hzero
      have hA_nonneg :
          0 ≤ |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * D.A| :=
        abs_nonneg _
      have hB_nonneg :
          0 ≤ |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * D.B| :=
        abs_nonneg _
      have hA_abs :
          |conclusion_poisson_cauchy_tv_second_order_norm_evenConstant * D.A| = 0 := by
        unfold conclusion_poisson_cauchy_tv_second_order_norm_tv at hzero
        unfold conclusion_poisson_cauchy_tv_second_order_norm_l1Norm at hzero
        unfold conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image at hzero
        linarith
      have hB_abs :
          |conclusion_poisson_cauchy_tv_second_order_norm_oddConstant * D.B| = 0 := by
        unfold conclusion_poisson_cauchy_tv_second_order_norm_tv at hzero
        unfold conclusion_poisson_cauchy_tv_second_order_norm_l1Norm at hzero
        unfold conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image at hzero
        linarith
      constructor
      · exact (mul_eq_zero.mp (abs_eq_zero.mp hA_abs)).resolve_left heven_ne
      · exact (mul_eq_zero.mp (abs_eq_zero.mp hB_abs)).resolve_left hodd_ne
    · rintro ⟨hA, hB⟩
      simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
        conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
        conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image, hA, hB]
  · simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
      conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
      conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image,
      abs_of_pos heven_pos]
  · simp [conclusion_poisson_cauchy_tv_second_order_norm_tv,
      conclusion_poisson_cauchy_tv_second_order_norm_l1Norm,
      conclusion_poisson_cauchy_tv_second_order_norm_linearL1Image,
      abs_of_pos hodd_pos]

end

end Omega.Conclusion
