import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

def lapseScaledMeasure {α : Type} (s : ℝ) (mu : α → ℝ) (A : α) : ℝ :=
  s * mu A

/-- Concrete lapse-time comparison data. `μ` is the reference gauge, `μN` is the lapse-twisted
gauge, and the fields record the uniform density comparison needed for the logarithmic `O(1)`
estimate. -/
structure LapseTimeGaugeInvarianceData where
  Event : Type
  mu : Event → ℝ
  muN : Event → ℝ
  c : ℝ
  C : ℝ
  c_pos : 0 < c
  c_le_one : c ≤ 1
  one_le_C : 1 ≤ C
  lower_compare : ∀ A : Event, lapseScaledMeasure (c : ℝ) (mu : Event → ℝ) A ≤ muN A
  upper_compare : ∀ A : Event, muN A ≤ lapseScaledMeasure (C : ℝ) (mu : Event → ℝ) A

namespace LapseTimeGaugeInvarianceData

lemma C_pos (D : LapseTimeGaugeInvarianceData) : 0 < D.C := by
  linarith [D.one_le_C]

/-- Uniform logarithmic control of the lapse-twisted measure. -/
def logMeasureChangeBound (D : LapseTimeGaugeInvarianceData) : Prop :=
  ∀ A : D.Event, 0 < D.mu A →
    |Real.log (D.muN A) - Real.log (D.mu A)| ≤ Real.log (D.C / D.c)

/-- Pairwise protocol-time comparisons change by at most a constant under the lapse gauge. -/
def asymptoticOrderInvariant (D : LapseTimeGaugeInvarianceData) : Prop :=
  ∀ A B : D.Event, 0 < D.mu A → 0 < D.mu B →
    |(Real.log (D.muN A) - Real.log (D.mu A)) -
        (Real.log (D.muN B) - Real.log (D.mu B))| ≤
      2 * Real.log (D.C / D.c)

lemma muN_pos (D : LapseTimeGaugeInvarianceData) {A : D.Event} (hmuA : 0 < D.mu A) :
    0 < D.muN A := by
  have hlower : lapseScaledMeasure D.c D.mu A ≤ D.muN A := D.lower_compare A
  have hprod : 0 < lapseScaledMeasure D.c D.mu A := by
    dsimp [lapseScaledMeasure]
    exact mul_pos D.c_pos hmuA
  linarith

lemma log_bound (D : LapseTimeGaugeInvarianceData) {A : D.Event} (hmuA : 0 < D.mu A) :
    |Real.log (D.muN A) - Real.log (D.mu A)| ≤ Real.log (D.C / D.c) := by
  have hmuNA : 0 < D.muN A := D.muN_pos hmuA
  have hlog_lower :
      Real.log D.c + Real.log (D.mu A) ≤ Real.log (D.muN A) := by
    have hcomp : lapseScaledMeasure D.c D.mu A ≤ D.muN A := D.lower_compare A
    have hprod_pos : 0 < lapseScaledMeasure D.c D.mu A := by
      dsimp [lapseScaledMeasure]
      exact mul_pos D.c_pos hmuA
    have hlog :
        Real.log (lapseScaledMeasure D.c D.mu A) ≤ Real.log (D.muN A) :=
      Real.log_le_log hprod_pos hcomp
    simpa [lapseScaledMeasure, Real.log_mul D.c_pos.ne' hmuA.ne'] using hlog
  have hlog_upper :
      Real.log (D.muN A) ≤ Real.log D.C + Real.log (D.mu A) := by
    have hcomp : D.muN A ≤ lapseScaledMeasure D.C D.mu A := D.upper_compare A
    have hprod_pos : 0 < lapseScaledMeasure D.C D.mu A := by
      dsimp [lapseScaledMeasure]
      exact mul_pos D.C_pos hmuA
    have hlog :
        Real.log (D.muN A) ≤ Real.log (lapseScaledMeasure D.C D.mu A) :=
      Real.log_le_log hmuNA hcomp
    simpa [lapseScaledMeasure, Real.log_mul D.C_pos.ne' hmuA.ne'] using hlog
  have hlog_c_nonpos : Real.log D.c ≤ 0 := by
    simpa using (Real.log_le_log D.c_pos D.c_le_one)
  have hlog_C_nonneg : 0 ≤ Real.log D.C := by
    simpa using (Real.log_le_log one_pos D.one_le_C)
  have hlog_div : Real.log (D.C / D.c) = Real.log D.C - Real.log D.c := by
    rw [div_eq_mul_inv, Real.log_mul D.C_pos.ne' (inv_ne_zero D.c_pos.ne')]
    simp [Real.log_inv]
    ring
  rw [abs_le, hlog_div]
  constructor
  · linarith
  · linarith

end LapseTimeGaugeInvarianceData

/-- Paper label: `cor:op-algebra-lapse-time-gauge-invariance`. Two-sided comparison of the lapse
twisted measure with the reference gauge gives a uniform logarithmic `O(1)` bound, hence every
pairwise protocol-time comparison changes by at most an additive constant. -/
theorem paper_op_algebra_lapse_time_gauge_invariance
    (D : LapseTimeGaugeInvarianceData) : D.logMeasureChangeBound ∧ D.asymptoticOrderInvariant := by
  refine ⟨?_, ?_⟩
  · intro A hmuA
    exact D.log_bound hmuA
  · intro A B hmuA hmuB
    have hA := D.log_bound hmuA
    have hB := D.log_bound hmuB
    have htriangle :
        |(Real.log (D.muN A) - Real.log (D.mu A)) -
            (Real.log (D.muN B) - Real.log (D.mu B))| ≤
          |Real.log (D.muN A) - Real.log (D.mu A)| +
            |Real.log (D.muN B) - Real.log (D.mu B)| := by
      let a := Real.log (D.muN A) - Real.log (D.mu A)
      let b := Real.log (D.muN B) - Real.log (D.mu B)
      have hnorm : ‖a + (-b)‖ ≤ ‖a‖ + ‖-b‖ := norm_add_le a (-b)
      have htriangle' : |a - b| ≤ |a| + |-b| := by
        simpa [a, b, sub_eq_add_neg, Real.norm_eq_abs] using hnorm
      simpa [a, b, abs_neg, abs_sub_comm] using htriangle'
    have hsum :
        |Real.log (D.muN A) - Real.log (D.mu A)| +
            |Real.log (D.muN B) - Real.log (D.mu B)| ≤
          2 * Real.log (D.C / D.c) := by
      linarith [hA, hB]
    exact le_trans htriangle hsum

end Omega.OperatorAlgebra
