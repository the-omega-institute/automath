import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.SyncKernelRealInput.FiniteRhTriangleDict

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Concrete modulus/radius data for the finite RH half-strip dictionary. -/
structure finite_rh_halfstrip_nopoles_data where
  lambda : ℝ
  mu : ℝ
  lambda_gt_one : 1 < lambda
  mu_ne_zero : mu ≠ 0

namespace finite_rh_halfstrip_nopoles_data

/-- The real part of the logarithmic pole parameter. -/
def finite_rh_halfstrip_nopoles_real_part (D : finite_rh_halfstrip_nopoles_data) : ℝ :=
  Real.log |D.mu| / Real.log D.lambda

/-- The open right half-strip from the finite RH dictionary. -/
def finite_rh_halfstrip_nopoles_halfstrip_condition (D : finite_rh_halfstrip_nopoles_data) : Prop :=
  1 / 2 < finite_rh_halfstrip_nopoles_real_part D ∧
    finite_rh_halfstrip_nopoles_real_part D < 1

/-- The equivalent modulus condition on a nontrivial spectral point. -/
def finite_rh_halfstrip_nopoles_ramanujan_violation (D : finite_rh_halfstrip_nopoles_data) : Prop :=
  Real.sqrt D.lambda < |D.mu| ∧ |D.mu| < D.lambda

/-- Half-strip pole-freeness is equivalent to excluding the Ramanujan-radius violation. -/
def holds (D : finite_rh_halfstrip_nopoles_data) : Prop :=
  (finite_rh_halfstrip_nopoles_halfstrip_condition D ↔
      finite_rh_halfstrip_nopoles_ramanujan_violation D) ∧
    (¬ finite_rh_halfstrip_nopoles_halfstrip_condition D ↔
      ¬ finite_rh_halfstrip_nopoles_ramanujan_violation D)

end finite_rh_halfstrip_nopoles_data

open finite_rh_halfstrip_nopoles_data

/-- Paper label: `cor:finite-rh-halfstrip-nopoles`. The real-part formula behind
`paper_finite_rh_triangle_dict` reduces the half-strip inequalities to logarithmic inequalities,
which are equivalent to the modulus window `sqrt(lambda) < |mu| < lambda` because `lambda > 1`.
-/
theorem paper_finite_rh_halfstrip_nopoles (D : finite_rh_halfstrip_nopoles_data) : D.holds := by
  have hlambda_pos : 0 < D.lambda := lt_trans zero_lt_one D.lambda_gt_one
  have habs_pos : 0 < |D.mu| := abs_pos.mpr D.mu_ne_zero
  have hsqrt_pos : 0 < Real.sqrt D.lambda := Real.sqrt_pos.mpr hlambda_pos
  have hlog_lambda_pos : 0 < Real.log D.lambda := Real.log_pos D.lambda_gt_one
  have hiff :
      finite_rh_halfstrip_nopoles_halfstrip_condition D ↔
        finite_rh_halfstrip_nopoles_ramanujan_violation D := by
    constructor
    · intro hhalf
      refine ⟨?_, ?_⟩
      · have hmul : (1 / 2 : ℝ) * Real.log D.lambda < Real.log |D.mu| := by
          exact (lt_div_iff₀ hlog_lambda_pos).mp hhalf.1
        have hlog : Real.log (Real.sqrt D.lambda) < Real.log |D.mu| := by
          rw [Real.log_sqrt hlambda_pos.le]
          nlinarith
        have hexp : Real.exp (Real.log (Real.sqrt D.lambda)) < Real.exp (Real.log |D.mu|) := by
          exact Real.exp_lt_exp.mpr hlog
        calc
          Real.sqrt D.lambda = Real.exp (Real.log (Real.sqrt D.lambda)) := by
            rw [Real.exp_log hsqrt_pos]
          _ < Real.exp (Real.log |D.mu|) := hexp
          _ = |D.mu| := by rw [Real.exp_log habs_pos]
      · have hlog : Real.log |D.mu| < Real.log D.lambda := by
          simpa using (div_lt_iff₀ hlog_lambda_pos).mp hhalf.2
        have hexp : Real.exp (Real.log |D.mu|) < Real.exp (Real.log D.lambda) := by
          exact Real.exp_lt_exp.mpr hlog
        calc
          |D.mu| = Real.exp (Real.log |D.mu|) := by rw [Real.exp_log habs_pos]
          _ < Real.exp (Real.log D.lambda) := hexp
          _ = D.lambda := by rw [Real.exp_log hlambda_pos]
    · intro hrad
      refine ⟨?_, ?_⟩
      · have hlog : Real.log (Real.sqrt D.lambda) < Real.log |D.mu| := by
          exact Real.strictMonoOn_log (by simpa using hsqrt_pos) (by simpa using habs_pos) hrad.1
        have hmul : (1 / 2 : ℝ) * Real.log D.lambda < Real.log |D.mu| := by
          rw [Real.log_sqrt hlambda_pos.le] at hlog
          nlinarith
        exact (lt_div_iff₀ hlog_lambda_pos).2 hmul
      · have hlog : Real.log |D.mu| < Real.log D.lambda := by
          exact Real.strictMonoOn_log (by simpa using habs_pos) (by simpa using hlambda_pos) hrad.2
        exact (div_lt_iff₀ hlog_lambda_pos).2 (by simpa using hlog)
  exact ⟨hiff, not_congr hiff⟩

end

end Omega.SyncKernelRealInput
