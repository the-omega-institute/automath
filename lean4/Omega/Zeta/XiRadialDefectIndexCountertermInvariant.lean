import Omega.Zeta.FiniteDefectCompleteReconstruction
import Omega.Zeta.XiRadialStokesCurvatureCountertermObstruction
import Omega.Zeta.XiSingleScaleRadialDeviationArcosh

namespace Omega.Zeta

/-- Paper label: `prop:xi-radial-defect-index-counterterm-invariant`. The two real outlier roots
give the concrete radial defect count and the common offcritical distance, while the affine radial
Stokes model shows that constant counterterms do not change the radial curvature. -/
theorem paper_xi_radial_defect_index_counterterm_invariant
    (κ : ℕ) (D : FiniteDefectCompleteReconstructionData κ)
    (L S c : ℝ) (hL : 1 < L) (hS : 2 < |S|) :
    let η := Real.arcosh (|S| / 2) / Real.log L
    let yPlus := (S + Real.sqrt (S ^ 2 - 4)) / 2
    let yMinus := (S - Real.sqrt (S ^ 2 - 4)) / 2
    let paper_xi_radial_defect_index_counterterm_invariant_defectIndex : ℕ := 2
    D.strictificationInvariant ∧
      paper_xi_radial_defect_index_counterterm_invariant_defectIndex = 2 ∧
      yPlus + 1 / yPlus = S ∧
      yMinus + 1 / yMinus = S ∧
      |Real.log (|yPlus|) / Real.log L| = η ∧
      |Real.log (|yMinus|) / Real.log L| = η ∧
      xi_radial_stokes_curvature_counterterm_obstruction_curvature c
          xi_radial_stokes_curvature_counterterm_obstruction_interval_zero =
        xi_radial_stokes_curvature_counterterm_obstruction_curvature 0
          xi_radial_stokes_curvature_counterterm_obstruction_interval_zero := by
  have hSsq_abs : 4 < |S| ^ 2 := by
    nlinarith
  have hSsq : 4 < S ^ 2 := by
    simpa [sq_abs] using hSsq_abs
  have hdisc_pos : 0 < S ^ 2 - 4 := by
    linarith
  have hdisc_nonneg : 0 ≤ S ^ 2 - 4 := le_of_lt hdisc_pos
  set Δ : ℝ := Real.sqrt (S ^ 2 - 4) with hΔ_def
  set yPlus : ℝ := (S + Δ) / 2 with hyPlus_def
  set yMinus : ℝ := (S - Δ) / 2 with hyMinus_def
  have hΔsq : Δ ^ 2 = S ^ 2 - 4 := by
    rw [hΔ_def, Real.sq_sqrt hdisc_nonneg]
  have hyPlus_quad : yPlus ^ 2 - S * yPlus + 1 = 0 := by
    rw [hyPlus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyMinus_quad : yMinus ^ 2 - S * yMinus + 1 = 0 := by
    rw [hyMinus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyProd : yPlus * yMinus = 1 := by
    rw [hyPlus_def, hyMinus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyPlus_ne : yPlus ≠ 0 := by
    intro hy0
    rw [hy0, zero_mul] at hyProd
    norm_num at hyProd
  have hyMinus_ne : yMinus ≠ 0 := by
    intro hy0
    rw [hy0, mul_zero] at hyProd
    norm_num at hyProd
  have hyPlus_eq : yPlus + 1 / yPlus = S := by
    have hyPlus_mul : yPlus ^ 2 + 1 = S * yPlus := by
      linarith [hyPlus_quad]
    have hdiv : yPlus + 1 / yPlus = (S * yPlus) / yPlus := by
      apply (eq_div_iff hyPlus_ne).2
      calc
        (yPlus + 1 / yPlus) * yPlus = yPlus ^ 2 + 1 := by
          field_simp [hyPlus_ne]
        _ = S * yPlus := hyPlus_mul
    calc
      yPlus + 1 / yPlus = (S * yPlus) / yPlus := hdiv
      _ = S := by field_simp [hyPlus_ne]
  have hyMinus_eq : yMinus + 1 / yMinus = S := by
    have hyMinus_mul : yMinus ^ 2 + 1 = S * yMinus := by
      linarith [hyMinus_quad]
    have hdiv : yMinus + 1 / yMinus = (S * yMinus) / yMinus := by
      apply (eq_div_iff hyMinus_ne).2
      calc
        (yMinus + 1 / yMinus) * yMinus = yMinus ^ 2 + 1 := by
          field_simp [hyMinus_ne]
        _ = S * yMinus := hyMinus_mul
    calc
      yMinus + 1 / yMinus = (S * yMinus) / yMinus := hdiv
      _ = S := by field_simp [hyMinus_ne]
  rcases paper_xi_finite_defect_complete_reconstruction κ D with ⟨_, _, _, hstrict⟩
  have hηPlus :
      |Real.log (|yPlus|) / Real.log L| = Real.arcosh (|S| / 2) / Real.log L := by
    simpa [hyPlus_def] using
      paper_xi_single_scale_radial_deviation_arcosh L S yPlus hL hyPlus_ne hyPlus_eq hS
  have hηMinus :
      |Real.log (|yMinus|) / Real.log L| = Real.arcosh (|S| / 2) / Real.log L := by
    simpa [hyMinus_def] using
      paper_xi_single_scale_radial_deviation_arcosh L S yMinus hL hyMinus_ne hyMinus_eq hS
  rcases paper_xi_radial_stokes_curvature_counterterm_obstruction with ⟨hcurvature, _, _⟩
  refine ⟨hstrict, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hyPlus_def] using hyPlus_eq
  · simpa [hyMinus_def] using hyMinus_eq
  · simpa using hηPlus
  · simpa using hηMinus
  · exact hcurvature c xi_radial_stokes_curvature_counterterm_obstruction_interval_zero

end Omega.Zeta
