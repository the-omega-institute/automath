import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart60ab2LogcmShiftProjector

namespace Omega.Zeta

noncomputable section

/-- Denominator of the normalized shift projector, kept under the corollary-specific prefix. -/
def xi_time_part60ab2_logcm_normalized_projector_bernoulli_denominator
    (q : ℕ → ℝ) (r : ℕ) : ℝ :=
  xi_time_part60ab2_logcm_shift_projector_denominator q r

/-- Normalized projector coefficient obtained by dividing by the spectral-gap product. -/
def xi_time_part60ab2_logcm_normalized_projector_bernoulli_projector
    (f q : ℕ → ℝ) (r : ℕ) : ℝ :=
  f r / xi_time_part60ab2_logcm_normalized_projector_bernoulli_denominator q r

/-- The scalar converting the normalized modal coefficient into the Bernoulli number. -/
def xi_time_part60ab2_logcm_normalized_projector_bernoulli_scale (r : ℕ) : ℝ :=
  (r : ℝ) * (2 * (r : ℝ) - 1) /
    (Real.goldenRatio⁻¹ + Real.goldenRatio ^ (2 * r - 3))

/-- Concrete normalized-projector Bernoulli recovery statement. -/
def xi_time_part60ab2_logcm_normalized_projector_bernoulli_statement : Prop :=
  ∀ f q a bernoulli : ℕ → ℝ,
    ∀ r : ℕ,
      1 ≤ r →
        (∀ j : ℕ, 1 ≤ j → j < r → q r ≠ q j) →
          f r = a r *
              xi_time_part60ab2_logcm_normalized_projector_bernoulli_denominator q r →
            bernoulli r =
                xi_time_part60ab2_logcm_normalized_projector_bernoulli_scale r * a r →
              xi_time_part60ab2_logcm_normalized_projector_bernoulli_projector f q r =
                  a r ∧
                bernoulli r =
                  xi_time_part60ab2_logcm_normalized_projector_bernoulli_scale r *
                    xi_time_part60ab2_logcm_normalized_projector_bernoulli_projector f q r

/-- Paper label: `cor:xi-time-part60ab2-logcm-normalized-projector-bernoulli`. Dividing the
shift-projector product identity by its nonzero spectral-gap product gives the normalized modal
coefficient, and the Bernoulli recovery formula follows by scalar substitution. -/
theorem paper_xi_time_part60ab2_logcm_normalized_projector_bernoulli :
    xi_time_part60ab2_logcm_normalized_projector_bernoulli_statement := by
  intro f q a bernoulli r hr hsep hf hbernoulli
  have hprojector :=
    paper_xi_time_part60ab2_logcm_shift_projector f q a r hr hsep
      (by
        simpa [xi_time_part60ab2_logcm_normalized_projector_bernoulli_denominator] using hf)
  have hnormalized :
      xi_time_part60ab2_logcm_normalized_projector_bernoulli_projector f q r = a r := by
    simpa [xi_time_part60ab2_logcm_normalized_projector_bernoulli_projector,
      xi_time_part60ab2_logcm_normalized_projector_bernoulli_denominator] using hprojector.2
  exact ⟨hnormalized, by rw [hbernoulli, hnormalized]⟩

end

end Omega.Zeta
