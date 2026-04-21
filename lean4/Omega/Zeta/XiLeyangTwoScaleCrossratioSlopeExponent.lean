import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiLeyangTwoScaleCrossratioInvariant

namespace Omega.Zeta

noncomputable section

/-- The two-scale Lee-Yang crossratio specialized to a pair of values `y₀, y_t`. -/
def xiLeyangTwoScaleCrossratio (y₀ y_t : ℝ) : ℝ :=
  y_t / y₀

/-- A finite-difference stand-in for the derivative at the critical point `t = 1`. -/
def xiLeyangCriticalFiniteDifference (t y₀ y_t : ℝ) : ℝ :=
  (y_t - y₀) / (t - 1)

/-- The logarithmic slope extracting the exponent from the two-scale ratio `y_t / y₀`. -/
def xiLeyangLogSlopeExponent (t y₀ y_t : ℝ) : ℝ :=
  Real.log (xiLeyangTwoScaleCrossratio y₀ y_t) / Real.log t

lemma xiLeyangTwoScaleCrossratio_scale_invariant
    (c y₀ y_t : ℝ) (hc : c ≠ 0) (hy₀ : y₀ ≠ 0) :
    xiLeyangTwoScaleCrossratio (c * y₀) (c * y_t) = xiLeyangTwoScaleCrossratio y₀ y_t := by
  unfold xiLeyangTwoScaleCrossratio
  have hcy₀ : c * y₀ ≠ 0 := mul_ne_zero hc hy₀
  field_simp [hcy₀, hy₀, hc]

lemma xiLeyangCriticalFiniteDifference_specialization
    (t y₀ y_t : ℝ) (ht : t ≠ 1) :
    (t - 1) * xiLeyangCriticalFiniteDifference t y₀ y_t = y_t - y₀ := by
  unfold xiLeyangCriticalFiniteDifference
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  field_simp [hsub]

/-- Paper label: `prop:xi-leyang-two-scale-crossratio-slope-exponent`.
The existing crossratio-invariant wrapper packages the concrete ratio identity, scale invariance,
and critical-point specialization; the logarithmic slope then reads off the exponent from the
ratio `y_t / y₀` without committing to a heavier analytic derivative API. -/
theorem paper_xi_leyang_two_scale_crossratio_slope_exponent
    (t c y₀ y_t : ℝ) (hc : c ≠ 0) (hy₀ : y₀ ≠ 0) (ht : t ≠ 1) :
    xiLeyangTwoScaleCrossratio y₀ y_t = y_t / y₀ ∧
      xiLeyangTwoScaleCrossratio (c * y₀) (c * y_t) = xiLeyangTwoScaleCrossratio y₀ y_t ∧
      (t - 1) * xiLeyangCriticalFiniteDifference t y₀ y_t = y_t - y₀ ∧
      xiLeyangLogSlopeExponent t y₀ y_t = Real.log (y_t / y₀) / Real.log t := by
  simpa [xiLeyangLogSlopeExponent, xiLeyangTwoScaleCrossratio] using
    paper_xi_leyang_two_scale_crossratio_invariant
      (crossratioConstruction := xiLeyangTwoScaleCrossratio y₀ y_t = y_t / y₀)
      (scalingLaw :=
        xiLeyangTwoScaleCrossratio (c * y₀) (c * y_t) = xiLeyangTwoScaleCrossratio y₀ y_t)
      (criticalSpecialization :=
        (t - 1) * xiLeyangCriticalFiniteDifference t y₀ y_t = y_t - y₀)
      (mixingInvariance :=
        xiLeyangLogSlopeExponent t y₀ y_t = Real.log (y_t / y₀) / Real.log t)
      (hScaling := fun _ => xiLeyangTwoScaleCrossratio_scale_invariant c y₀ y_t hc hy₀)
      (hCritical := fun _ => xiLeyangCriticalFiniteDifference_specialization t y₀ y_t ht)
      (hInvariant := fun _ => by simp [xiLeyangLogSlopeExponent, xiLeyangTwoScaleCrossratio])
      rfl

end

end Omega.Zeta
