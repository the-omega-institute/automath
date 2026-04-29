import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- Two-step renormalization ratio `R_q = r_q / r_{q-2}`. -/
noncomputable def pom_two_step_renorm_fixed_point_loglaw_R (r : ℕ → ℝ) (q : ℕ) : ℝ :=
  r q / r (q - 2)

/-- Two-step complex-mode modulus `η_q = |μ_q| / r_{q-2}`. -/
noncomputable def pom_two_step_renorm_fixed_point_loglaw_eta (r μ : ℕ → ℝ) (q : ℕ) : ℝ :=
  |μ q| / r (q - 2)

/-- Aitken residual modulus `δ_q = |μ_q| / r_q`. -/
noncomputable def pom_two_step_renorm_fixed_point_loglaw_delta (r μ : ℕ → ℝ) (q : ℕ) : ℝ :=
  |μ q| / r q

/-- Complex gap exponent `g_q = 1 - log |μ_q| / log r_q`. -/
noncomputable def pom_two_step_renorm_fixed_point_loglaw_gap (r μ : ℕ → ℝ) (q : ℕ) : ℝ :=
  1 - Real.log |μ q| / Real.log (r q)

/-- Product form of the complex gap, the quantity appearing in the logarithmic law. -/
noncomputable def pom_two_step_renorm_fixed_point_loglaw_gap_log (r μ : ℕ → ℝ)
    (q : ℕ) : ℝ :=
  pom_two_step_renorm_fixed_point_loglaw_gap r μ q * Real.log (r q)

/-- Concrete package for the two-step rescaling identity and its limiting logarithmic
consequence.  The hypotheses keep the Perron scale positive and away from `1`, so the
displayed logarithmic exponent is nondegenerate. -/
def pom_two_step_renorm_fixed_point_loglaw_statement : Prop :=
  ∀ (r μ : ℕ → ℝ) (Rlim : ℝ),
    1 < Rlim →
      (∀ q, 0 < r q) →
        (∀ q, r q ≠ 1) →
          (∀ q, μ q ≠ 0) →
            (∀ q,
              pom_two_step_renorm_fixed_point_loglaw_eta r μ q =
                  pom_two_step_renorm_fixed_point_loglaw_R r q *
                    pom_two_step_renorm_fixed_point_loglaw_delta r μ q ∧
                Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q) =
                  Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q) -
                    pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q) ∧
              (Tendsto (fun q => Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q))
                  atTop (𝓝 (Real.log Rlim)) →
                Tendsto (fun q => Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q))
                  atTop (𝓝 0) →
                  Tendsto (fun q => pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q)
                    atTop (𝓝 (Real.log Rlim)) ∧
                    Tendsto
                      (fun q => pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q /
                        Real.log Rlim) atTop (𝓝 1))

/-- Paper label: `prop:pom-two-step-renorm-fixed-point-loglaw`. -/
theorem paper_pom_two_step_renorm_fixed_point_loglaw :
    pom_two_step_renorm_fixed_point_loglaw_statement := by
  intro r μ Rlim hRlim hr hr_ne_one hμ
  constructor
  · intro q
    have hrq_ne : r q ≠ 0 := ne_of_gt (hr q)
    have hrqm_ne : r (q - 2) ≠ 0 := ne_of_gt (hr (q - 2))
    have hμ_abs_ne : |μ q| ≠ 0 := abs_ne_zero.mpr (hμ q)
    have hlog_ne : Real.log (r q) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (hr q) (hr_ne_one q)
    constructor
    · unfold pom_two_step_renorm_fixed_point_loglaw_eta
        pom_two_step_renorm_fixed_point_loglaw_R
        pom_two_step_renorm_fixed_point_loglaw_delta
      field_simp [hrq_ne, hrqm_ne]
    · unfold pom_two_step_renorm_fixed_point_loglaw_eta
        pom_two_step_renorm_fixed_point_loglaw_R
        pom_two_step_renorm_fixed_point_loglaw_gap_log
        pom_two_step_renorm_fixed_point_loglaw_gap
      rw [Real.log_div hμ_abs_ne hrqm_ne, Real.log_div hrq_ne hrqm_ne]
      field_simp [hlog_ne]
      ring
  · intro hR hEta
    have hdiff :
        Tendsto
          (fun q =>
            Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q) -
              Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q))
          atTop (𝓝 (Real.log Rlim - 0)) :=
      hR.sub hEta
    have hEq :
        (fun q => pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q) =ᶠ[atTop]
          fun q =>
            Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q) -
              Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q) := by
      filter_upwards with q
      have hlog :=
        (show
          Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q) =
            Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q) -
              pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q from
            (show
              pom_two_step_renorm_fixed_point_loglaw_eta r μ q =
                  pom_two_step_renorm_fixed_point_loglaw_R r q *
                    pom_two_step_renorm_fixed_point_loglaw_delta r μ q ∧
                Real.log (pom_two_step_renorm_fixed_point_loglaw_eta r μ q) =
                  Real.log (pom_two_step_renorm_fixed_point_loglaw_R r q) -
                    pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q from
                  (by
                    have hrq_ne : r q ≠ 0 := ne_of_gt (hr q)
                    have hrqm_ne : r (q - 2) ≠ 0 := ne_of_gt (hr (q - 2))
                    have hμ_abs_ne : |μ q| ≠ 0 := abs_ne_zero.mpr (hμ q)
                    have hlog_ne : Real.log (r q) ≠ 0 :=
                      Real.log_ne_zero_of_pos_of_ne_one (hr q) (hr_ne_one q)
                    constructor
                    · unfold pom_two_step_renorm_fixed_point_loglaw_eta
                        pom_two_step_renorm_fixed_point_loglaw_R
                        pom_two_step_renorm_fixed_point_loglaw_delta
                      field_simp [hrq_ne, hrqm_ne]
                    · unfold pom_two_step_renorm_fixed_point_loglaw_eta
                        pom_two_step_renorm_fixed_point_loglaw_R
                        pom_two_step_renorm_fixed_point_loglaw_gap_log
                        pom_two_step_renorm_fixed_point_loglaw_gap
                      rw [Real.log_div hμ_abs_ne hrqm_ne, Real.log_div hrq_ne hrqm_ne]
                      field_simp [hlog_ne]
                      ring)).2)
      linarith
    have hGap :
        Tendsto (fun q => pom_two_step_renorm_fixed_point_loglaw_gap_log r μ q)
          atTop (𝓝 (Real.log Rlim)) := by
      simpa using hdiff.congr' hEq.symm
    refine ⟨hGap, ?_⟩
    have hlogRlim_ne : Real.log Rlim ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (lt_trans zero_lt_one hRlim) (ne_of_gt hRlim)
    have hNorm :=
      hGap.div_const (Real.log Rlim)
    simpa [hlogRlim_ne] using hNorm

end Omega.POM
