import Mathlib.Tactic
import Omega.Conclusion.LogsobolevMixingForcesCriticalLocalization

namespace Omega.Conclusion

open Omega.OperatorAlgebra

/-- Concrete HZOM package: one-sided contraction data, one off-axis zero witness, and one visible
gap family whose exact lower-bound profile is recorded explicitly. -/
structure conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_data
    where
  alpha : ℝ
  lam : ℝ
  theta : ℝ
  kappa : ℝ
  beta : ℝ
  gamma : ℝ
  multiplicity : ℕ
  amplitude : ℝ
  visibleGap : ℕ → ℝ
  logsobolev_certificate : hzomLogSobolevDecayCertificate alpha kappa
  reflection_certificate : hzomReflectionSymmetricZeroSet lam theta kappa
  off_axis_zero : hzomZeroAt lam theta gamma
  off_axis_abscissa : hzomCriticalAbscissa < beta
  amplitude_pos : 0 < amplitude
  visibleGap_closed :
    ∀ T : ℕ,
      visibleGap T =
        amplitude * (T : ℝ) ^ (multiplicity - 1) *
          Real.exp ((beta - hzomCriticalAbscissa) * T)

/-- The conclusion-level localization datum attached to the one-sided contraction hypothesis. -/
def conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_localization_data
    (h : conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_data) :
    conclusion_logsobolev_mixing_forces_critical_localization_data where
  alpha := h.alpha
  lam := h.lam
  theta := h.theta
  kappa := h.kappa
  logsobolev_certificate := h.logsobolev_certificate
  reflection_certificate := h.reflection_certificate

/-- One-sided contraction forces critical-line concentration, hence forbids an off-axis HZOM zero
event at the chosen abscissa `β`; conversely, the off-axis witness data supplies the stated
exponential lower bound for the visible distinguisher family. -/
def conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_statement
    (h : conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_data) :
    Prop :=
  hzomCriticalLineConcentration h.lam h.theta h.kappa ∧
    ¬ hzomCommutingPolarZeroEvent h.lam h.theta h.kappa h.beta h.gamma ∧
    hzomZeroAt h.lam h.theta h.gamma ∧
    (∃ c : ℝ,
      0 < c ∧
        ∀ T : ℕ,
          1 ≤ T →
            c * (T : ℝ) ^ (h.multiplicity - 1) *
                Real.exp ((h.beta - hzomCriticalAbscissa) * T) ≤
              h.visibleGap T) ∧
    hzomCriticalAbscissa < h.beta

/-- Paper label: `thm:conclusion-hzom-one-sided-contraction-exponential-distinguisher-
incompatibility`. The conclusion-level log-Sobolev localization theorem turns the one-sided
contraction hypothesis into critical-line concentration. This immediately excludes any off-axis
HZOM zero event. The recorded off-axis witness package simultaneously yields the required
exponential lower bound for the visible distinguisher family. -/
theorem paper_conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility
    (h : conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_data) :
    conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_statement h := by
  rcases paper_conclusion_logsobolev_mixing_forces_critical_localization
      (conclusion_hzom_one_sided_contraction_exponential_distinguisher_incompatibility_localization_data
        h) with ⟨_, _, hcritical, _⟩
  refine ⟨hcritical, ?_, h.off_axis_zero, ?_, h.off_axis_abscissa⟩
  · intro hzero
    have hbeta : h.beta = hzomCriticalAbscissa := hcritical hzero
    exact (ne_of_lt h.off_axis_abscissa) hbeta.symm
  · refine ⟨h.amplitude, h.amplitude_pos, ?_⟩
    intro T hT
    simp [h.visibleGap_closed T]

end Omega.Conclusion
