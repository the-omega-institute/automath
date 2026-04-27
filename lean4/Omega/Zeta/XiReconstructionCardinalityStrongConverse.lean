import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Concrete data for the xi-reconstruction cardinality strong converse. The finite protocol has
`sideStates` external states and sees `visibleCard` visible symbols at depth `m`; its success is
bounded by the number of distinguishable pairs divided by the binary source volume. The final field
is the Binet/asymptotic interface used by downstream statements. -/
structure xi_reconstruction_cardinality_strong_converse_data where
  xi_reconstruction_cardinality_strong_converse_m : ℕ
  xi_reconstruction_cardinality_strong_converse_sideStates : ℝ
  xi_reconstruction_cardinality_strong_converse_visibleCard : ℝ
  xi_reconstruction_cardinality_strong_converse_successProb : ℝ
  xi_reconstruction_cardinality_strong_converse_threshold : ℝ
  xi_reconstruction_cardinality_strong_converse_fibModel : ℕ → ℝ
  xi_reconstruction_cardinality_strong_converse_binetLimit : ℝ
  xi_reconstruction_cardinality_strong_converse_sideStates_pos :
    0 < xi_reconstruction_cardinality_strong_converse_sideStates
  xi_reconstruction_cardinality_strong_converse_visibleCard_pos :
    0 < xi_reconstruction_cardinality_strong_converse_visibleCard
  xi_reconstruction_cardinality_strong_converse_threshold_pos :
    0 < xi_reconstruction_cardinality_strong_converse_threshold
  xi_reconstruction_cardinality_strong_converse_success_le_cardinality :
    xi_reconstruction_cardinality_strong_converse_successProb ≤
      xi_reconstruction_cardinality_strong_converse_sideStates *
        xi_reconstruction_cardinality_strong_converse_visibleCard /
          (2 : ℝ) ^ xi_reconstruction_cardinality_strong_converse_m
  xi_reconstruction_cardinality_strong_converse_threshold_le_success :
    xi_reconstruction_cardinality_strong_converse_threshold ≤
      xi_reconstruction_cardinality_strong_converse_successProb
  xi_reconstruction_cardinality_strong_converse_binet_asymptotic :
    Tendsto
      (fun n : ℕ =>
        xi_reconstruction_cardinality_strong_converse_fibModel n /
          Real.rpow Real.goldenRatio n)
      atTop
      (𝓝 xi_reconstruction_cardinality_strong_converse_binetLimit)

/-- The finite cardinality success bound `P <= M * |X_m| / 2^m`. -/
def xi_reconstruction_cardinality_strong_converse_cardinality_bound
    (D : xi_reconstruction_cardinality_strong_converse_data) : Prop :=
  D.xi_reconstruction_cardinality_strong_converse_successProb ≤
    D.xi_reconstruction_cardinality_strong_converse_sideStates *
      D.xi_reconstruction_cardinality_strong_converse_visibleCard /
        (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m

/-- The logarithmic lower bound forced by a positive success threshold. -/
def xi_reconstruction_cardinality_strong_converse_logarithmic_lower_bound
    (D : xi_reconstruction_cardinality_strong_converse_data) : Prop :=
  Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_threshold +
      D.xi_reconstruction_cardinality_strong_converse_m -
      Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_visibleCard ≤
    Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_sideStates

/-- The Binet/asymptotic interface carried by the reconstruction theorem. -/
def xi_reconstruction_cardinality_strong_converse_binet_clause
    (D : xi_reconstruction_cardinality_strong_converse_data) : Prop :=
  Tendsto
    (fun n : ℕ =>
      D.xi_reconstruction_cardinality_strong_converse_fibModel n /
        Real.rpow Real.goldenRatio n)
    atTop
    (𝓝 D.xi_reconstruction_cardinality_strong_converse_binetLimit)

/-- Combined paper-facing claim. -/
def xi_reconstruction_cardinality_strong_converse_claim
    (D : xi_reconstruction_cardinality_strong_converse_data) : Prop :=
  xi_reconstruction_cardinality_strong_converse_cardinality_bound D ∧
    xi_reconstruction_cardinality_strong_converse_logarithmic_lower_bound D ∧
      xi_reconstruction_cardinality_strong_converse_binet_clause D

/-- Paper label: `cor:xi-reconstruction-cardinality-strong-converse`. -/
theorem paper_xi_reconstruction_cardinality_strong_converse
    (D : xi_reconstruction_cardinality_strong_converse_data) :
    xi_reconstruction_cardinality_strong_converse_claim D := by
  have hpow_pos :
      0 < (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m := by
    positivity
  have hthreshold_card :
      D.xi_reconstruction_cardinality_strong_converse_threshold ≤
        D.xi_reconstruction_cardinality_strong_converse_sideStates *
          D.xi_reconstruction_cardinality_strong_converse_visibleCard /
            (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m :=
    le_trans D.xi_reconstruction_cardinality_strong_converse_threshold_le_success
      D.xi_reconstruction_cardinality_strong_converse_success_le_cardinality
  have hmul :
      D.xi_reconstruction_cardinality_strong_converse_threshold *
          (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m ≤
        D.xi_reconstruction_cardinality_strong_converse_sideStates *
          D.xi_reconstruction_cardinality_strong_converse_visibleCard := by
    have hmul' :=
      mul_le_mul_of_nonneg_right hthreshold_card (le_of_lt hpow_pos)
    simpa [div_mul_eq_mul_div, hpow_pos.ne'] using hmul'
  have hnormalized :
      D.xi_reconstruction_cardinality_strong_converse_threshold *
            (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m /
          D.xi_reconstruction_cardinality_strong_converse_visibleCard ≤
        D.xi_reconstruction_cardinality_strong_converse_sideStates := by
    rw [div_le_iff₀ D.xi_reconstruction_cardinality_strong_converse_visibleCard_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hnormalized_pos :
      0 <
        D.xi_reconstruction_cardinality_strong_converse_threshold *
            (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m /
          D.xi_reconstruction_cardinality_strong_converse_visibleCard := by
    exact div_pos
      (mul_pos D.xi_reconstruction_cardinality_strong_converse_threshold_pos hpow_pos)
      D.xi_reconstruction_cardinality_strong_converse_visibleCard_pos
  have hlog :
      Real.logb 2
          (D.xi_reconstruction_cardinality_strong_converse_threshold *
              (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m /
            D.xi_reconstruction_cardinality_strong_converse_visibleCard) ≤
        Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_sideStates :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hnormalized_pos hnormalized
  have hlog_form :
      Real.logb 2
          (D.xi_reconstruction_cardinality_strong_converse_threshold *
              (2 : ℝ) ^ D.xi_reconstruction_cardinality_strong_converse_m /
            D.xi_reconstruction_cardinality_strong_converse_visibleCard) =
        Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_threshold +
          D.xi_reconstruction_cardinality_strong_converse_m -
          Real.logb 2 D.xi_reconstruction_cardinality_strong_converse_visibleCard := by
    rw [Real.logb_div
        (mul_ne_zero
          D.xi_reconstruction_cardinality_strong_converse_threshold_pos.ne'
          hpow_pos.ne')
        D.xi_reconstruction_cardinality_strong_converse_visibleCard_pos.ne',
      Real.logb_mul D.xi_reconstruction_cardinality_strong_converse_threshold_pos.ne'
        hpow_pos.ne',
      Real.logb_pow]
    simp
  refine ⟨?_, ?_, ?_⟩
  · exact D.xi_reconstruction_cardinality_strong_converse_success_le_cardinality
  · simpa [xi_reconstruction_cardinality_strong_converse_logarithmic_lower_bound, hlog_form] using
      hlog
  · exact D.xi_reconstruction_cardinality_strong_converse_binet_asymptotic

end Omega.Zeta
