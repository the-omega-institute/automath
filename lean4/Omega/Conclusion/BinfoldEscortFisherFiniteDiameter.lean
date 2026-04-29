import Mathlib.Tactic
import Omega.Conclusion.BinfoldEscortSqrtCircleArc

namespace Omega.Conclusion

noncomputable section

lemma conclusion_binfold_escort_fisher_finite_diameter_alpha_nonneg (q : ℕ) :
    0 ≤ conclusion_binfold_escort_sqrt_circle_arc_alpha q := by
  unfold conclusion_binfold_escort_sqrt_circle_arc_alpha
  exact Real.arctan_nonneg.mpr (Real.sqrt_nonneg _)

lemma conclusion_binfold_escort_fisher_finite_diameter_alpha_le_zero_endpoint (q : ℕ) :
    conclusion_binfold_escort_sqrt_circle_arc_alpha q ≤
      conclusion_binfold_escort_sqrt_circle_arc_alpha 0 := by
  unfold conclusion_binfold_escort_sqrt_circle_arc_alpha
    conclusion_binfold_escort_sqrt_circle_arc_u
  apply Real.arctan_mono
  apply Real.sqrt_le_sqrt
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_le_pow : Real.goldenRatio ≤ Real.goldenRatio ^ (q + 1) := by
    simpa using
      (pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) (show 1 ≤ q + 1 by omega))
  have hpow_pos : 0 < Real.goldenRatio ^ (q + 1) := by positivity
  have hrecip : 1 / Real.goldenRatio ^ (q + 1) ≤ 1 / Real.goldenRatio :=
    one_div_le_one_div_of_le hphi_pos hphi_le_pow
  simpa using hrecip

/-- Paper label: `cor:conclusion-binfold-escort-fisher-finite-diameter`. -/
theorem paper_conclusion_binfold_escort_fisher_finite_diameter :
    ∃ C : ℝ,
      C = 2 * Real.arctan (Real.sqrt (1 / Real.goldenRatio)) ∧
        ∀ q : ℕ,
          2 * |conclusion_binfold_escort_sqrt_circle_arc_alpha 0 -
            conclusion_binfold_escort_sqrt_circle_arc_alpha q| ≤ C := by
  refine ⟨2 * Real.arctan (Real.sqrt (1 / Real.goldenRatio)), rfl, ?_⟩
  intro q
  have hnonneg := conclusion_binfold_escort_fisher_finite_diameter_alpha_nonneg q
  have hle := conclusion_binfold_escort_fisher_finite_diameter_alpha_le_zero_endpoint q
  have hzero :
      conclusion_binfold_escort_sqrt_circle_arc_alpha 0 =
        Real.arctan (Real.sqrt (1 / Real.goldenRatio)) := by
    simp [conclusion_binfold_escort_sqrt_circle_arc_alpha,
      conclusion_binfold_escort_sqrt_circle_arc_u]
  have habs :
      |conclusion_binfold_escort_sqrt_circle_arc_alpha 0 -
        conclusion_binfold_escort_sqrt_circle_arc_alpha q| ≤
          conclusion_binfold_escort_sqrt_circle_arc_alpha 0 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith
  nlinarith [habs, conclusion_binfold_escort_fisher_finite_diameter_alpha_nonneg 0]

end

end Omega.Conclusion
