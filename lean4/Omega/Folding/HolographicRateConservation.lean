import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Omega.Folding.HolographicRateConservation

open Real Finset

variable {α : Type*}

/-- Aggregated code length `m_agg(S) = -log₂ ∑_{ω∈S} 2^(-m ω)`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
noncomputable def mAgg (S : Finset α) (m : α → ℝ) : ℝ :=
  -Real.logb 2 (∑ ω ∈ S, (2 : ℝ) ^ (-m ω))

/-- Minimum code length `m_min(S) = min_{ω∈S} m ω`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
noncomputable def mMin (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) : ℝ :=
  S.inf' hS m

private lemma two_rpow_pos (a : ℝ) : (0 : ℝ) < (2 : ℝ) ^ a :=
  Real.rpow_pos_of_pos (by norm_num) a

/-- Lower bound: `2^(-m_min) ≤ ∑ 2^(-m ω)`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem sum_ge_two_pow_neg_min (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    (2 : ℝ) ^ (-mMin S hS m) ≤ ∑ ω ∈ S, (2 : ℝ) ^ (-m ω) := by
  obtain ⟨ω, hω, hmin⟩ := S.exists_mem_eq_inf' hS m
  have hmem : (2 : ℝ) ^ (-m ω) ≤ ∑ ω' ∈ S, (2 : ℝ) ^ (-m ω') := by
    refine Finset.single_le_sum (f := fun ω' => (2 : ℝ) ^ (-m ω')) ?_ hω
    intro ω' _
    exact (two_rpow_pos _).le
  have heq : mMin S hS m = m ω := by unfold mMin; exact hmin
  rw [heq]
  exact hmem

/-- Upper bound: `∑ 2^(-m ω) ≤ |S| · 2^(-m_min)`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem sum_le_card_mul_two_pow_neg_min (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    (∑ ω ∈ S, (2 : ℝ) ^ (-m ω)) ≤ (S.card : ℝ) * (2 : ℝ) ^ (-mMin S hS m) := by
  have hpt : ∀ ω ∈ S, (2 : ℝ) ^ (-m ω) ≤ (2 : ℝ) ^ (-mMin S hS m) := by
    intro ω hω
    have hmge : mMin S hS m ≤ m ω := by
      unfold mMin
      exact Finset.inf'_le _ hω
    have hneg : -m ω ≤ -mMin S hS m := by linarith
    exact Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hneg
  have := Finset.sum_le_sum hpt
  simpa [Finset.sum_const, nsmul_eq_mul] using this

/-- Upper bound on `m_agg`: `m_agg ≤ m_min`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem mAgg_le_mMin (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    mAgg S m ≤ mMin S hS m := by
  have hge := sum_ge_two_pow_neg_min S hS m
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-mMin S hS m) := two_rpow_pos _
  have hsum_pos : (0 : ℝ) < ∑ ω ∈ S, (2 : ℝ) ^ (-m ω) := lt_of_lt_of_le hpos hge
  have h1 : Real.logb 2 ((2 : ℝ) ^ (-mMin S hS m)) ≤
      Real.logb 2 (∑ ω ∈ S, (2 : ℝ) ^ (-m ω)) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hge
  have h2 : Real.logb 2 ((2 : ℝ) ^ (-mMin S hS m)) = -mMin S hS m := by
    rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  unfold mAgg
  linarith [h1, h2]

/-- Lower bound on `m_agg`: `m_min - log₂ |S| ≤ m_agg`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem mAgg_ge_mMin_sub_logb (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    mMin S hS m - Real.logb 2 (S.card : ℝ) ≤ mAgg S m := by
  have hle := sum_le_card_mul_two_pow_neg_min S hS m
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast hS.card_pos
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-mMin S hS m) := two_rpow_pos _
  have hprod_pos : (0 : ℝ) < (S.card : ℝ) * (2 : ℝ) ^ (-mMin S hS m) :=
    mul_pos hcard_pos hpow_pos
  have hsum_pos : (0 : ℝ) < ∑ ω ∈ S, (2 : ℝ) ^ (-m ω) := by
    have := sum_ge_two_pow_neg_min S hS m
    exact lt_of_lt_of_le (two_rpow_pos _) this
  have h1 : Real.logb 2 (∑ ω ∈ S, (2 : ℝ) ^ (-m ω)) ≤
      Real.logb 2 ((S.card : ℝ) * (2 : ℝ) ^ (-mMin S hS m)) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hsum_pos hle
  have h2 : Real.logb 2 ((S.card : ℝ) * (2 : ℝ) ^ (-mMin S hS m)) =
      Real.logb 2 (S.card : ℝ) + (-mMin S hS m) := by
    rw [Real.logb_mul (ne_of_gt hcard_pos) (ne_of_gt hpow_pos)]
    rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  unfold mAgg
  linarith [h1, h2]

/-- Two-sided bound: `|m_agg - m_min| ≤ log₂ |S|`.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem abs_mAgg_sub_mMin_le (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    |mAgg S m - mMin S hS m| ≤ Real.logb 2 (S.card : ℝ) := by
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hcard_ge_one : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hlog_nn : (0 : ℝ) ≤ Real.logb 2 (S.card : ℝ) :=
    Real.logb_nonneg (by norm_num) hcard_ge_one
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have h1 := mAgg_le_mMin S hS m
    linarith
  · have := mAgg_ge_mMin_sub_logb S hS m
    linarith

/-- Paper package: holographic rate conservation.
    prop:fold-subexp-multiplicity-holographic-rate-conservation -/
theorem paper_fold_subexp_multiplicity_holographic_rate_conservation
    (S : Finset α) (hS : S.Nonempty) (m : α → ℝ) :
    |mAgg S m - mMin S hS m| ≤ Real.logb 2 (S.card : ℝ) :=
  abs_mAgg_sub_mMin_le S hS m

end Omega.Folding.HolographicRateConservation
