import Omega.SPG.GodelBoundaryDecodingRelativeErrorThreshold
import Omega.SPG.SingleParamLogReadoutPigeonhole
import Mathlib.Tactic

namespace Omega.SPG

open Finset
open Omega.SPG.SingleParamLogReadoutPigeonhole

private theorem weightedSum_nonneg {k : ℕ} (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin k → Bool) : 0 ≤ weightedSum w b := by
  unfold weightedSum
  refine sum_nonneg fun i _ => ?_
  by_cases hbi : b i <;> simp [hbi, (hw i).le]

private theorem weightedSum_le_total {k : ℕ} (w : Fin k → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin k → Bool) : weightedSum w b ≤ ∑ i, w i := by
  unfold weightedSum
  refine sum_le_sum fun i _ => ?_
  by_cases hbi : b i <;> simp [hbi, (hw i).le]

private theorem totalWeight_pos {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) :
    0 < ∑ i, w i := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      have h0 : 0 < w 0 := hw 0
      have hle : w 0 ≤ ∑ i, w i := by
        exact single_le_sum (fun i _ => (hw i).le) (by simp)
      linarith

private theorem bucketCount_pos_nat {k : ℕ} (hk : 1 ≤ k) : 0 < 2 ^ k - 1 := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      have hpow : 1 < 2 ^ Nat.succ n := by
        simpa using one_lt_pow' (show 1 < (2 : ℕ) by decide) (Nat.succ_ne_zero n)
      omega

private theorem bucketCount_pos {k : ℕ} (hk : 1 ≤ k) : 0 < ((2 : ℝ) ^ k - 1) := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      rw [pow_succ]
      have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast Nat.one_le_pow n 2 (by decide : 0 < 2)
      nlinarith

private theorem exists_close_weighted_sums {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℝ)
    (hw : ∀ i, 0 < w i) :
    ∃ b b' : Fin k → Bool, b ≠ b' ∧
      |weightedSum w b - weightedSum w b'| ≤ (∑ i, w i) / ((2 : ℝ) ^ k - 1) := by
  classical
  let total : ℝ := ∑ i, w i
  let bucketCount : ℕ := 2 ^ k - 1
  let δ : ℝ := total / ((2 : ℝ) ^ k - 1)
  have htotal_pos : 0 < total := totalWeight_pos hk w hw
  have hbucketCount_pos_nat : 0 < bucketCount := bucketCount_pos_nat hk
  have hbucketCount_pos : 0 < ((2 : ℝ) ^ k - 1) := bucketCount_pos hk
  have hδ_pos : 0 < δ := by
    dsimp [δ, total]
    positivity
  by_contra hclose
  have hsep :
      ∀ b b' : Fin k → Bool,
        b ≠ b' → δ < |weightedSum w b - weightedSum w b'| := by
    intro b b' hbb'
    have hnot :
        ¬ |weightedSum w b - weightedSum w b'| ≤ δ := by
      intro hle
      exact hclose ⟨b, b', hbb', by simpa [δ] using hle⟩
    exact lt_of_not_ge hnot
  let bucket : (Fin k → Bool) → Fin bucketCount := fun b =>
    let x := weightedSum w b
    if hx : x = 0 then
      ⟨0, hbucketCount_pos_nat⟩
    else
      ⟨Nat.pred ⌈x / δ⌉₊, by
        have hx_nonneg : 0 ≤ x := weightedSum_nonneg w hw b
        have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx)
        have hx_le_total : x ≤ total := by
          simpa [total] using weightedSum_le_total w hw b
        have hceil_le : ⌈x / δ⌉₊ ≤ bucketCount := by
          apply Nat.ceil_le.mpr
          have hbucketCount_cast : (bucketCount : ℝ) = (2 : ℝ) ^ k - 1 := by
            norm_num [bucketCount]
          rw [div_le_iff₀ hδ_pos]
          rw [hbucketCount_cast]
          dsimp [δ]
          field_simp [hbucketCount_pos.ne']
          linarith
        have hceil_pos : 0 < ⌈x / δ⌉₊ := by
          exact Nat.ceil_pos.2 (div_pos hx_pos hδ_pos)
        exact lt_of_lt_of_le (Nat.pred_lt (Nat.pos_iff_ne_zero.mp hceil_pos)) hceil_le⟩
  have hbucket_inj : Function.Injective bucket := by
    intro b b' hEq
    by_contra hne
    let x := weightedSum w b
    let y := weightedSum w b'
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · have hxy : x = y := by simpa [hx, hy]
        have habs : |weightedSum w b - weightedSum w b'| ≤ δ := by
          simpa [x, y, hxy, hδ_pos.le]
        linarith [hsep b b' hne, (by simpa [x, y] using habs)]
      · have hbucket0 : (bucket b).val = 0 := by simp [bucket, x, hx]
        have hbucket0' : (bucket b').val = 0 := by
          simpa [hEq] using hbucket0
        have hy_nonneg : 0 ≤ y := weightedSum_nonneg w hw b'
        have hy_pos : 0 < y := lt_of_le_of_ne hy_nonneg (Ne.symm hy)
        have hceil_eq : ⌈y / δ⌉₊ = 1 := by
          have hyceil_pos : 0 < ⌈y / δ⌉₊ := Nat.ceil_pos.2 (div_pos hy_pos hδ_pos)
          have hpred : Nat.pred ⌈y / δ⌉₊ = 0 := by
            simpa [bucket, y, hy] using hbucket0'
          have hsub : ⌈y / δ⌉₊ - 1 = 0 := by
            simpa [Nat.pred_eq_sub_one] using hpred
          omega
        have hy_le : y ≤ δ := by
          have h1 : ⌈y / δ⌉₊ ≤ 1 := by simpa [hceil_eq]
          have hy_ratio_le : y / δ ≤ ((1 : ℕ) : ℝ) := Nat.ceil_le.mp h1
          rw [div_le_iff₀ hδ_pos] at hy_ratio_le
          simpa using hy_ratio_le
        have habs : |x - y| ≤ δ := by
          simpa [hx, abs_of_nonneg hy_nonneg] using hy_le
        linarith [hsep b b' hne, (by simpa [x, y] using habs)]
    · by_cases hy : y = 0
      · have habs : |y - x| ≤ δ := by
          have hbucket0 : (bucket b').val = 0 := by simp [bucket, y, hy]
          have hbucket0' : (bucket b).val = 0 := by
            simpa [hEq] using hbucket0
          have hx_nonneg : 0 ≤ x := weightedSum_nonneg w hw b
          have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx)
          have hceil_eq : ⌈x / δ⌉₊ = 1 := by
            have hxceil_pos : 0 < ⌈x / δ⌉₊ := Nat.ceil_pos.2 (div_pos hx_pos hδ_pos)
            have hpred : Nat.pred ⌈x / δ⌉₊ = 0 := by
              simpa [bucket, x, hx] using hbucket0'
            have hsub : ⌈x / δ⌉₊ - 1 = 0 := by
              simpa [Nat.pred_eq_sub_one] using hpred
            omega
          have hx_le : x ≤ δ := by
            have h1 : ⌈x / δ⌉₊ ≤ 1 := by simpa [hceil_eq]
            have hx_ratio_le : x / δ ≤ ((1 : ℕ) : ℝ) := Nat.ceil_le.mp h1
            rw [div_le_iff₀ hδ_pos] at hx_ratio_le
            simpa using hx_ratio_le
          simpa [hy, abs_sub_comm, abs_of_nonneg hx_nonneg] using hx_le
        have habs' : |x - y| ≤ δ := by simpa [abs_sub_comm] using habs
        linarith [hsep b b' hne, (by simpa [x, y] using habs')]
      · have hx_pos : 0 < x := by
          have hx_nonneg : 0 ≤ x := weightedSum_nonneg w hw b
          exact lt_of_le_of_ne hx_nonneg (Ne.symm hx)
        have hy_pos : 0 < y := by
          have hy_nonneg : 0 ≤ y := weightedSum_nonneg w hw b'
          exact lt_of_le_of_ne hy_nonneg (Ne.symm hy)
        have hvals : (bucket b).val = (bucket b').val := congrArg Fin.val hEq
        have hceil_eq : ⌈x / δ⌉₊ = ⌈y / δ⌉₊ := by
          have hxceil_pos : 0 < ⌈x / δ⌉₊ := Nat.ceil_pos.2 (div_pos hx_pos hδ_pos)
          have hyceil_pos : 0 < ⌈y / δ⌉₊ := Nat.ceil_pos.2 (div_pos hy_pos hδ_pos)
          have hpred_eq : Nat.pred ⌈x / δ⌉₊ = Nat.pred ⌈y / δ⌉₊ := by
            simpa [bucket, x, y, hx, hy] using hvals
          have hsub_eq : ⌈x / δ⌉₊ - 1 = ⌈y / δ⌉₊ - 1 := by
            simpa [Nat.pred_eq_sub_one] using hpred_eq
          omega
        let c : ℕ := ⌈x / δ⌉₊
        have hx_upper : x / δ ≤ c := by
          exact Nat.ceil_le.mp (by simp [c])
        have hy_upper : y / δ ≤ c := by
          exact Nat.ceil_le.mp (by simpa [c, hceil_eq])
        have hx_lower : (((c - 1 : ℕ) : ℝ) < x / δ) := by
          have hc_pos : 0 < c := by
            simpa [c] using Nat.ceil_pos.2 (div_pos hx_pos hδ_pos)
          have hc_lt : c - 1 < c := Nat.sub_lt hc_pos (show 0 < (1 : ℕ) by decide)
          have hx_lower_nat : c - 1 < ⌈x / δ⌉₊ := by simpa [c] using hc_lt
          exact (Nat.lt_ceil).1 hx_lower_nat
        have hy_lower : (((c - 1 : ℕ) : ℝ) < y / δ) := by
          have hc_pos : 0 < c := by
            simpa [c, hceil_eq] using Nat.ceil_pos.2 (div_pos hy_pos hδ_pos)
          have hc_lt : c - 1 < c := Nat.sub_lt hc_pos (show 0 < (1 : ℕ) by decide)
          have hy_lower_nat : c - 1 < ⌈y / δ⌉₊ := by simpa [c, hceil_eq] using hc_lt
          exact (Nat.lt_ceil).1 hy_lower_nat
        have hx_upper' : x ≤ c * δ := by
          rw [div_le_iff₀ hδ_pos] at hx_upper
          simpa [mul_comm, mul_left_comm, mul_assoc] using hx_upper
        have hy_upper' : y ≤ c * δ := by
          rw [div_le_iff₀ hδ_pos] at hy_upper
          simpa [mul_comm, mul_left_comm, mul_assoc] using hy_upper
        have hx_lower' : (((c - 1 : ℕ) : ℝ) * δ < x) := by
          rw [lt_div_iff₀ hδ_pos] at hx_lower
          simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lower
        have hy_lower' : (((c - 1 : ℕ) : ℝ) * δ < y) := by
          rw [lt_div_iff₀ hδ_pos] at hy_lower
          simpa [mul_comm, mul_left_comm, mul_assoc] using hy_lower
        have hc_pos : 0 < c := by
          simpa [c] using Nat.ceil_pos.2 (div_pos hx_pos hδ_pos)
        have hstep : (((c - 1 : ℕ) : ℝ) * δ) + δ = (c : ℝ) * δ := by
          have hcast : (((c - 1 : ℕ) : ℝ) + 1) = (c : ℝ) := by
            have hnat : (c - 1 + 1 : ℕ) = c := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hc_pos)
            have hnatR : (((c - 1 + 1 : ℕ) : ℝ)) = (c : ℝ) := by
              exact_mod_cast hnat
            simpa [Nat.cast_add] using hnatR
          nlinarith
        have hleft : -δ ≤ x - y := by
          have hlt : -δ < x - y := by
            nlinarith [hx_lower', hy_upper', hstep]
          linarith
        have hright : x - y ≤ δ := by
          have hlt : x - y < δ := by
            nlinarith [hx_upper', hy_lower', hstep]
          linarith
        have habs : |x - y| ≤ δ := abs_le.2 ⟨hleft, hright⟩
        linarith [hsep b b' hne, (by simpa [x, y] using habs)]
  have hcard := Fintype.card_le_of_injective bucket hbucket_inj
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin] at hcard
  omega

/-- Paper package for the arbitrary-`k` log-readout pigeonhole bound together with the existing
relative-error decoding wrapper.
    thm:spg-single-parameter-log-readout-vs-diagonal-multichannel-bifurcation -/
theorem paper_spg_single_parameter_log_readout_vs_diagonal_multichannel_bifurcation {k : ℕ}
    (hk : 1 ≤ k) (p : Fin k → ℝ) (hp : ∀ i, 1 < p i) (ε pmin : ℝ) (exactDecoding : Prop)
    (hε : 0 < ε) (hpmin : 1 < pmin) (hThreshold : ε < (pmin - 1) / (pmin + 1))
    (hDecode : ε < (pmin - 1) / (pmin + 1) → exactDecoding) :
    (∃ b b' : Fin k → Bool, b ≠ b' ∧
      |weightedSum (fun i => Real.log (p i)) b - weightedSum (fun i => Real.log (p i)) b'| ≤
        (∑ i, Real.log (p i)) / ((2 : ℝ) ^ k - 1)) ∧ exactDecoding := by
  refine ⟨?_, ?_⟩
  · apply exists_close_weighted_sums hk (fun i => Real.log (p i))
    intro i
    exact Real.log_pos (hp i)
  · exact paper_spg_godel_boundary_decoding_relative_error_threshold ε pmin exactDecoding hε hpmin
      hThreshold hDecode

end Omega.SPG
