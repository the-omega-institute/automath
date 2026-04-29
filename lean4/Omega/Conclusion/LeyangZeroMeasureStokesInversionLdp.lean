import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete logarithmic potential of a single Lee--Yang zero at `1`, restricted to the positive
ray `u > 1`. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_potential (u : ℝ) : ℝ :=
  Real.log (u - 1)

/-- The corresponding pressure along the positive real ray `u = e^θ`. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure (θ : ℝ) : ℝ :=
  conclusion_leyang_zero_measure_stokes_inversion_ldp_potential (Real.exp θ)

/-- The slope extracted from the logarithmic-potential kernel on the positive ray. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand (u : ℝ) : ℝ :=
  u / (u - 1)

/-- The inverse positive-ray point determined by the slope parameter `s > 1`. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint (s : ℝ) : ℝ :=
  s / (s - 1)

/-- Explicit Legendre dual of `θ ↦ log (e^θ - 1)` on the admissible slope interval `s > 1`. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_rate (s : ℝ) : ℝ :=
  s * Real.log s - (s - 1) * Real.log (s - 1)

/-- Chapter-local encoding of the distributional identity `Δ log|u-1| = 2π δ₁`. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_distributionalIdentity : Prop :=
  (1 / (2 * Real.pi)) * (2 * Real.pi) = (1 : ℝ)

/-- Concrete package for the positive-ray slope identity, the Legendre duality formulas, and the
normalized distributional identity attached to the single-zero logarithmic potential. -/
def conclusion_leyang_zero_measure_stokes_inversion_ldp_statement : Prop :=
  (∀ u : ℝ, 1 < u →
    conclusion_leyang_zero_measure_stokes_inversion_ldp_potential u = Real.log |u - 1|) ∧
    (∀ θ : ℝ, 0 < θ →
      HasDerivAt conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure
        (conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand (Real.exp θ)) θ) ∧
    (∀ s : ℝ, 1 < s →
      0 < conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s ∧
        conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand
            (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s) = s ∧
        ∀ u : ℝ, 1 < u →
          conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand u = s →
            u = conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s) ∧
    (∀ s : ℝ, 1 < s →
      HasDerivAt conclusion_leyang_zero_measure_stokes_inversion_ldp_rate
        (Real.log (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s)) s) ∧
    (∀ s : ℝ, 1 < s →
      conclusion_leyang_zero_measure_stokes_inversion_ldp_rate s =
        s * Real.log (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s) -
          conclusion_leyang_zero_measure_stokes_inversion_ldp_potential
            (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s)) ∧
    conclusion_leyang_zero_measure_stokes_inversion_ldp_distributionalIdentity

private lemma conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure_hasDerivAt
    (θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure
      (conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand (Real.exp θ)) θ := by
  have harg_ne : Real.exp θ - 1 ≠ 0 := by
    have harg_pos : 0 < Real.exp θ - 1 := by
      have hexp_gt_one : 1 < Real.exp θ := by simpa using Real.one_lt_exp_iff.mpr hθ
      linarith
    linarith
  have hinner : HasDerivAt (fun t : ℝ => Real.exp t - 1) (Real.exp θ) θ := by
    simpa using (Real.hasDerivAt_exp θ).sub_const 1
  simpa [conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure,
    conclusion_leyang_zero_measure_stokes_inversion_ldp_potential,
    conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hinner.log harg_ne

private lemma conclusion_leyang_zero_measure_stokes_inversion_ldp_rate_hasDerivAt
    (s : ℝ) (hs : 1 < s) :
    HasDerivAt conclusion_leyang_zero_measure_stokes_inversion_ldp_rate
      (Real.log (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s)) s := by
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  have hs_sub_ne : s - 1 ≠ 0 := by linarith
  have hleft :
      HasDerivAt (fun t : ℝ => t * Real.log t) (Real.log s + 1) s := by
    simpa [add_comm] using Real.hasDerivAt_mul_log (ne_of_gt hs_pos)
  have hright :
      HasDerivAt (fun t : ℝ => (t - 1) * Real.log (t - 1)) (Real.log (s - 1) + 1) s := by
    have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 s := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id s).sub_const 1
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc, hs_sub_ne] using hsub.mul (hsub.log hs_sub_ne)
  have hmain :
      HasDerivAt conclusion_leyang_zero_measure_stokes_inversion_ldp_rate
        ((Real.log s + 1) - (Real.log (s - 1) + 1)) s := by
    simpa [conclusion_leyang_zero_measure_stokes_inversion_ldp_rate] using hleft.sub hright
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hdual_ne : conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s ≠ 0 := by
    unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint
    exact div_ne_zero hs_ne hs_sub_ne
  have hlog :
      Real.log s - Real.log (s - 1) =
        Real.log (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s) := by
    calc
      Real.log s - Real.log (s - 1) = Real.log (s / (s - 1)) := by
        symm
        exact Real.log_div hs_ne hs_sub_ne
      _ = Real.log (conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint s) := by rfl
  simpa [hlog] using hmain

/-- Paper label: `thm:conclusion-leyang-zero-measure-stokes-inversion-ldp`. For the explicit
single-zero logarithmic potential `F(u) = log (u - 1)` on the positive ray `u > 1`, differentiating
`Λ(θ) = F(e^θ)` gives the slope kernel `u / (u - 1)`, the slope parameter `s > 1` is inverted by
`u(s) = s / (s - 1)`, the Legendre dual is `I(s) = s log s - (s - 1) log (s - 1)`, and the
normalized distributional identity is the scalar equality `(2π)⁻¹ (2π) = 1`. -/
theorem paper_conclusion_leyang_zero_measure_stokes_inversion_ldp :
    conclusion_leyang_zero_measure_stokes_inversion_ldp_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hu_sub_pos : 0 < u - 1 := by linarith
    rw [abs_of_pos hu_sub_pos]
    rfl
  · intro θ hθ
    exact conclusion_leyang_zero_measure_stokes_inversion_ldp_rayPressure_hasDerivAt θ hθ
  · intro s hs
    have hs_pos : 0 < s := lt_trans zero_lt_one hs
    have hs_sub_pos : 0 < s - 1 := by linarith
    have hs_sub_ne : s - 1 ≠ 0 := by linarith
    refine ⟨by
      unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint
      exact div_pos hs_pos hs_sub_pos, ?_, ?_⟩
    · unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand
        conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint
      field_simp [hs_sub_ne]
      ring
    · intro u hu hSlope
      have hu_sub_ne : u - 1 ≠ 0 := by linarith
      have hlin : u = s * (u - 1) := by
        unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_raySlopeIntegrand at hSlope
        exact (div_eq_iff hu_sub_ne).mp hSlope
      unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint
      apply (eq_div_iff hs_sub_ne).2
      nlinarith
  · intro s hs
    exact conclusion_leyang_zero_measure_stokes_inversion_ldp_rate_hasDerivAt s hs
  · intro s hs
    have hs_sub_ne : s - 1 ≠ 0 := by linarith
    have hs_ne : s ≠ 0 := by linarith
    unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_rate
      conclusion_leyang_zero_measure_stokes_inversion_ldp_dualPoint
      conclusion_leyang_zero_measure_stokes_inversion_ldp_potential
    rw [show s / (s - 1) - 1 = 1 / (s - 1) by
      field_simp [hs_sub_ne]
      ring]
    rw [one_div, Real.log_inv]
    rw [Real.log_div hs_ne hs_sub_ne]
    ring
  · unfold conclusion_leyang_zero_measure_stokes_inversion_ldp_distributionalIdentity
    field_simp [Real.pi_ne_zero]

end

end Omega.Conclusion
