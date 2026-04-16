import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Conclusion.JGEllipseConditionNumberThreshold

namespace Omega.Conclusion.JGEllipseFixedEpsilonInformationBarrier

open Real
open Omega.Conclusion.JGEllipseConditionNumberThreshold

private theorem sqrt_succ_sub_sqrt_le_half_inv_sqrt (N : ℕ) (hN : 0 < N) :
    Real.sqrt (N + 1) - Real.sqrt N ≤ 1 / (2 * Real.sqrt N) := by
  have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtN1_pos : 0 < Real.sqrt (N + 1) := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.succ_pos _
  have hsplit :
      Real.sqrt (N + 1) - Real.sqrt N = 1 / (Real.sqrt (N + 1) + Real.sqrt N) := by
    apply (eq_div_iff (by positivity)).2
    have hsqN : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsqN1 : (Real.sqrt (N + 1)) ^ 2 = (N + 1 : ℝ) := Real.sq_sqrt (by positivity)
    nlinarith
  have hsqrt_mono : Real.sqrt N ≤ Real.sqrt (N + 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hden :
      2 * Real.sqrt N ≤ Real.sqrt (N + 1) + Real.sqrt N := by
    nlinarith
  rw [hsplit]
  have htwo_pos : 0 < 2 * Real.sqrt N := by positivity
  exact one_div_le_one_div_of_le htwo_pos hden

private theorem reciprocal_gap_le_sqrt_gap (N : ℕ) (hN : 0 < N) :
    1 / Real.sqrt N - 1 / Real.sqrt (N + 1) ≤ Real.sqrt (N + 1) - Real.sqrt N := by
  have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtN1_pos : 0 < Real.sqrt (N + 1) := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.succ_pos _
  have hsqrtN_ge_one : (1 : ℝ) ≤ Real.sqrt N := by
    have hsqN : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [hsqN, Real.sqrt_nonneg N, hN']
  have hsqrtN1_ge_one : (1 : ℝ) ≤ Real.sqrt (N + 1) := by
    have hsqN1 : (Real.sqrt (N + 1)) ^ 2 = (N + 1 : ℝ) := Real.sq_sqrt (by positivity)
    have hN1' : (1 : ℝ) ≤ N + 1 := by nlinarith
    nlinarith [hsqN1, Real.sqrt_nonneg (N + 1), hN1']
  have hprod_ge_one : (1 : ℝ) ≤ Real.sqrt N * Real.sqrt (N + 1) := by
    nlinarith
  have hnum_nonneg : 0 ≤ Real.sqrt (N + 1) - Real.sqrt N := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith
  calc
    1 / Real.sqrt N - 1 / Real.sqrt (N + 1)
        = (Real.sqrt (N + 1) - Real.sqrt N) / (Real.sqrt N * Real.sqrt (N + 1)) := by
            field_simp [hsqrtN_pos.ne', hsqrtN1_pos.ne']
    _ ≤ Real.sqrt (N + 1) - Real.sqrt N := by
          exact div_le_self hnum_nonneg hprod_ge_one

private theorem successive_axis_gap_bound (N : ℕ) (hN : 0 < N) :
    max
      |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
      |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
      ≤ 1 / Real.sqrt N := by
  have hsqrt_gap :
      Real.sqrt (N + 1) - Real.sqrt N ≤ 1 / (2 * Real.sqrt N) :=
    sqrt_succ_sub_sqrt_le_half_inv_sqrt N hN
  have hrec_gap :
      1 / Real.sqrt N - 1 / Real.sqrt (N + 1) ≤ 1 / (2 * Real.sqrt N) := by
    calc
      1 / Real.sqrt N - 1 / Real.sqrt (N + 1)
          ≤ Real.sqrt (N + 1) - Real.sqrt N := reciprocal_gap_le_sqrt_gap N hN
      _ ≤ 1 / (2 * Real.sqrt N) := hsqrt_gap
  have hsqrt_nonneg : 0 ≤ Real.sqrt (N + 1) - Real.sqrt N := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsqrt_mono : Real.sqrt N ≤ Real.sqrt (N + 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hsqrtN_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsqrtN1_pos : 0 < Real.sqrt (N + 1) := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.succ_pos _
  have hrec_gap' :
      (Real.sqrt N)⁻¹ - (Real.sqrt (N + 1))⁻¹ ≤ 1 / (2 * Real.sqrt N) := by
    simpa [one_div] using hrec_gap
  have hrec_nonneg : 0 ≤ (Real.sqrt N)⁻¹ - (Real.sqrt (N + 1))⁻¹ := by
    have hrec_le :
        (Real.sqrt (N + 1))⁻¹ ≤ (Real.sqrt N)⁻¹ := by
      exact inv_anti₀ hsqrtN_pos hsqrt_mono
    exact sub_nonneg.mpr hrec_le
  have ha :
      |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
        ≤ 1 / Real.sqrt N := by
    calc
      |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
          = |(Real.sqrt (N + 1) - Real.sqrt N) +
              ((Real.sqrt (N + 1))⁻¹ - (Real.sqrt N)⁻¹)| := by
                congr 1
                ring
      _ ≤ |Real.sqrt (N + 1) - Real.sqrt N| +
            |(Real.sqrt (N + 1))⁻¹ - (Real.sqrt N)⁻¹| := abs_add_le _ _
      _ = (Real.sqrt (N + 1) - Real.sqrt N) +
            ((Real.sqrt N)⁻¹ - (Real.sqrt (N + 1))⁻¹) := by
            rw [abs_of_nonneg hsqrt_nonneg, abs_sub_comm, abs_of_nonneg hrec_nonneg]
      _ ≤ 1 / (2 * Real.sqrt N) + 1 / (2 * Real.sqrt N) := by
            exact add_le_add hsqrt_gap hrec_gap'
      _ = 1 / Real.sqrt N := by
            field_simp
            ring
  have hb :
      |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
        ≤ 1 / Real.sqrt N := by
    calc
      |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
          = |(Real.sqrt (N + 1) - Real.sqrt N) +
              ((Real.sqrt N)⁻¹ - (Real.sqrt (N + 1))⁻¹)| := by
                congr 1
                ring
      _ = (Real.sqrt (N + 1) - Real.sqrt N) +
            ((Real.sqrt N)⁻¹ - (Real.sqrt (N + 1))⁻¹) := by
            rw [abs_of_nonneg (add_nonneg hsqrt_nonneg hrec_nonneg)]
      _ ≤ 1 / (2 * Real.sqrt N) + 1 / (2 * Real.sqrt N) := by
            exact add_le_add hsqrt_gap hrec_gap'
      _ = 1 / Real.sqrt N := by
            field_simp
            ring
  exact max_le ha hb

/-- For any fixed absolute error floor, sufficiently large neighboring ellipse parameters overlap.
    cor:conclusion-jg-ellipse-fixed-epsilon-information-barrier -/
theorem paper_conclusion_jg_ellipse_fixed_epsilon_information_barrier
    (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∃ aTilde bTilde : ℝ,
      |aTilde - (Real.sqrt N + (Real.sqrt N)⁻¹)| ≤ ε0 ∧
      |aTilde - (Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹)| ≤ ε0 ∧
      |bTilde - (Real.sqrt N - (Real.sqrt N)⁻¹)| ≤ ε0 ∧
      |bTilde - (Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹)| ≤ ε0 := by
  refine ⟨max 1 (Nat.ceil ((ε0⁻¹) ^ 2)), ?_⟩
  intro N hN
  have hN_ge_one : 1 ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hN_pos : 0 < N := lt_of_lt_of_le (by decide : 0 < 1) hN_ge_one
  have hlower :
      (ε0⁻¹ : ℝ) ^ 2 ≤ N := by
    have hceil : (ε0⁻¹ : ℝ) ^ 2 ≤ Nat.ceil ((ε0⁻¹) ^ 2) := by
      exact Nat.le_ceil ((ε0⁻¹) ^ 2)
    have hN' : (Nat.ceil ((ε0⁻¹) ^ 2) : ℝ) ≤ N := by
      exact_mod_cast le_trans (Nat.le_max_right _ _) hN
    exact le_trans hceil hN'
  have hsqrt_lower : ε0⁻¹ ≤ Real.sqrt N := by
    have hsqN : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
    have hsqrtN_nonneg : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
    nlinarith [hlower, hsqN, hsqrtN_nonneg]
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN_pos)
  have hbound : 1 / Real.sqrt N ≤ ε0 := by
    exact (one_div_le hsqrt_pos hε0).2 (by simpa [one_div] using hsqrt_lower)
  have hgap :
      max
        |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
        |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
        ≤ 2 * ε0 := by
    calc
      max
        |(Real.sqrt (N + 1) + (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N + (Real.sqrt N)⁻¹)|
        |(Real.sqrt (N + 1) - (Real.sqrt (N + 1))⁻¹) - (Real.sqrt N - (Real.sqrt N)⁻¹)|
          ≤ 1 / Real.sqrt N := successive_axis_gap_bound N hN_pos
      _ ≤ ε0 := hbound
      _ ≤ 2 * ε0 := by nlinarith
  exact paper_conclusion_jg_ellipse_condition_number_overlap_criterion N ε0 hgap

end Omega.Conclusion.JGEllipseFixedEpsilonInformationBarrier
