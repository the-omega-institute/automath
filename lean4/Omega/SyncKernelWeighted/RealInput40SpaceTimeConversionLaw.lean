import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete bookkeeping for the quadratic finite-part / pole-gap comparison along one imaginary
slice.  The `t⁴` remainders are kept explicit so that the conversion law is an exact algebraic
recombination of the two Taylor expansions. -/
structure real_input_40_space_time_conversion_law_data where
  real_input_40_space_time_conversion_law_logLambda : ℝ
  real_input_40_space_time_conversion_law_directionalCoupling : ℝ
  real_input_40_space_time_conversion_law_metricCoeff : ℝ
  real_input_40_space_time_conversion_law_finitepartCoeff : ℝ
  real_input_40_space_time_conversion_law_finitepartDrift : ℝ → ℝ
  real_input_40_space_time_conversion_law_poleGap : ℝ → ℝ
  real_input_40_space_time_conversion_law_finitepartRemainder : ℝ → ℝ
  real_input_40_space_time_conversion_law_poleGapRemainder : ℝ → ℝ
  real_input_40_space_time_conversion_law_logLambda_pos :
    0 < real_input_40_space_time_conversion_law_logLambda
  real_input_40_space_time_conversion_law_coupling_eq :
    real_input_40_space_time_conversion_law_finitepartCoeff =
      real_input_40_space_time_conversion_law_directionalCoupling *
        real_input_40_space_time_conversion_law_metricCoeff
  real_input_40_space_time_conversion_law_finitepart_expansion :
    ∀ t : ℝ,
      real_input_40_space_time_conversion_law_finitepartDrift t =
        (t ^ 2 / 2) * real_input_40_space_time_conversion_law_finitepartCoeff +
          t ^ 4 * real_input_40_space_time_conversion_law_finitepartRemainder t
  real_input_40_space_time_conversion_law_pole_gap_expansion :
    ∀ t : ℝ,
      real_input_40_space_time_conversion_law_poleGap t =
        (t ^ 2 / (2 * real_input_40_space_time_conversion_law_logLambda)) *
            real_input_40_space_time_conversion_law_metricCoeff +
          t ^ 4 * real_input_40_space_time_conversion_law_poleGapRemainder t

/-- The exact `t⁴` correction left after matching the two quadratic leading terms. -/
def real_input_40_space_time_conversion_law_remainder
    (D : real_input_40_space_time_conversion_law_data) (t : ℝ) : ℝ :=
  D.real_input_40_space_time_conversion_law_finitepartRemainder t -
    (D.real_input_40_space_time_conversion_law_logLambda *
        D.real_input_40_space_time_conversion_law_directionalCoupling) *
      D.real_input_40_space_time_conversion_law_poleGapRemainder t

/-- Paper-facing conversion law: the finite-part drift equals the leading conversion constant times
the pole gap, plus an explicit `t⁴` correction assembled from the two Taylor remainders. -/
def real_input_40_space_time_conversion_law_statement
    (D : real_input_40_space_time_conversion_law_data) : Prop :=
  ∀ t : ℝ,
    D.real_input_40_space_time_conversion_law_finitepartDrift t =
      (D.real_input_40_space_time_conversion_law_logLambda *
          D.real_input_40_space_time_conversion_law_directionalCoupling) *
        D.real_input_40_space_time_conversion_law_poleGap t +
      t ^ 4 * real_input_40_space_time_conversion_law_remainder D t

/-- Paper label: `prop:real-input-40-space-time-conversion-law`. -/
theorem paper_real_input_40_space_time_conversion_law
    (D : real_input_40_space_time_conversion_law_data) :
    real_input_40_space_time_conversion_law_statement D := by
  intro t
  have hlog_ne : D.real_input_40_space_time_conversion_law_logLambda ≠ 0 :=
    ne_of_gt D.real_input_40_space_time_conversion_law_logLambda_pos
  rw [D.real_input_40_space_time_conversion_law_finitepart_expansion t,
    D.real_input_40_space_time_conversion_law_pole_gap_expansion t,
    real_input_40_space_time_conversion_law_remainder,
    D.real_input_40_space_time_conversion_law_coupling_eq]
  field_simp [hlog_ne]
  ring

end Omega.SyncKernelWeighted
