import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.Conclusion.ContinuousPressureFrontDominatesDiscreteCertificate

open Filter Topology

namespace Omega.Conclusion

/-- Fixed-confidence log budget specialized to the `1 / (m + 1)` scale. -/
noncomputable def conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget
    (ε : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1)⁻¹ * Real.log (1 / ε)

/-- Continuous left-endpoint branch specialized to the linear zero at `γ_*`. -/
noncomputable def conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front
    (γStar ε : ℝ) (m : ℕ) : ℝ :=
  continuousPressureFront
    (fun t => t * γStar)
    (conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε m)

/-- Paper label: `cor:conclusion-fixed-confidence-continuous-certificate-typical-fiber-limit`.
For the linearized rate family with unique zero `γ_*`, the fixed-confidence front is the
generalized inverse of the continuous rate, decreases along the `m ↦ log(1 / ε) / (m + 1)` budget,
and converges to `γ_*`. -/
theorem paper_conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit
    (γStar ε : ℝ) (hεpos : 0 < ε) (hεlt : ε < 1) :
    (∀ m,
      continuousPressureFrontInverseIdentity
        (fun t => t * γStar)
        (conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε m)) ∧
    (∀ m,
      conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε (m + 1) ≤
        conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε m) ∧
    Tendsto
      (conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε)
      atTop
      (𝓝 γStar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    simpa [conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget] using
      (paper_conclusion_continuous_pressure_front_dominates_discrete_certificate
        (Λ := fun t => t * γStar)
        (Φ := fun q => ((q : ℝ) - 1) * γStar)
        (c := conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε m)
        (by intro q hq; rfl)).1
  · intro m
    have hlog_nonneg : 0 ≤ Real.log (1 / ε) := by
      exact Real.log_nonneg (le_of_lt ((one_lt_div hεpos).2 hεlt))
    have hstep_inv : (1 : ℝ) / ((m : ℝ) + 2) ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
      exact
        (one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (m : ℝ) + 1)
          (by linarith : (m : ℝ) + 1 < (m : ℝ) + 2)).le
    have hstep :
        (((m : ℝ) + 2)⁻¹) * Real.log (1 / ε) ≤ (((m : ℝ) + 1)⁻¹) * Real.log (1 / ε) := by
      simpa [one_div] using (mul_le_mul_of_nonneg_right hstep_inv hlog_nonneg)
    have hfront_formula :
        ∀ n : ℕ,
          conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε n =
            γStar +
              conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε n := by
      intro n
      unfold conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front
        continuousPressureFront continuousPressureBranch
      ring
    have hfront_succ :
        conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε
            (m + 1) =
          γStar + (((m : ℝ) + 2)⁻¹) * Real.log (1 / ε) := by
      rw [hfront_formula]
      unfold conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget
      have hcast : (((m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) + 2 := by
        norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
      rw [hcast]
    have hfront_now :
        conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε m =
          γStar + (((m : ℝ) + 1)⁻¹) * Real.log (1 / ε) := by
      rw [hfront_formula]
      rfl
    rw [hfront_succ, hfront_now]
    nlinarith
  · have hshift : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
      simpa using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hshift
    have hbudget :
        Tendsto
          (conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε)
          atTop
          (𝓝 0) := by
      unfold conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget
      have hmul :
          Tendsto
            (fun m : ℕ => Real.log (1 / ε) * ((m : ℝ) + 1)⁻¹)
            atTop
            (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hinv :
          Tendsto
            (fun m : ℕ => Real.log (1 / ε) * ((m : ℝ) + 1)⁻¹)
            atTop
            (𝓝 (Real.log (1 / ε) * 0)))
      simpa [mul_comm] using hmul
    have hfront :
        conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front γStar ε =
          fun m : ℕ =>
            γStar +
              conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_budget ε m := by
      funext m
      unfold conclusion_fixed_confidence_continuous_certificate_typical_fiber_limit_front
        continuousPressureFront continuousPressureBranch
      ring
    rw [hfront]
    simpa using tendsto_const_nhds.add hbudget

end Omega.Conclusion
