import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMTrace3SpectralNormExtremal

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

noncomputable section

lemma gm_trace3_near_extremal_clustering_lower_envelope_mono {n : ℕ} (hn : 1 ≤ n)
    {S1 x xstar : ℝ} (hS1 : 0 ≤ S1)
    (hx : S1 / ((n + 1 : ℕ) : ℝ) ≤ x) (hxx : x ≤ xstar) :
    gmTrace3LowerEnvelope (n + 1) S1 x ≤ gmTrace3LowerEnvelope (n + 1) S1 xstar := by
  have hm : 2 ≤ n + 1 := by omega
  let u : ℝ := x - S1 / ((n + 1 : ℕ) : ℝ)
  let v : ℝ := xstar - S1 / ((n + 1 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have huv : u ≤ v := by dsimp [u, v]; linarith
  have hmono :=
    (Omega.SyncKernelWeighted.paper_gm_trace3_spectral_norm_extremal
      (n + 1) hm (S1 := S1) (S3 := 0) (u := u) (v := v) hS1 hu huv).1
  simpa [u, v, sub_add_cancel] using hmono

lemma gm_trace3_near_extremal_clustering_tail_cube_gap_identity {n : ℕ}
    (tail : Fin n → ℝ) (barY : ℝ) (hsum : ∑ i, tail i = (n : ℝ) * barY) :
    (∑ i, (tail i - barY) ^ 2 * (tail i + 2 * barY)) =
      (∑ i, (tail i) ^ 3) - (n : ℝ) * barY ^ 3 := by
  calc
    (∑ i, (tail i - barY) ^ 2 * (tail i + 2 * barY)) =
        ∑ i, ((tail i) ^ 3 - 3 * barY ^ 2 * tail i + 2 * barY ^ 3) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = (∑ i, (tail i) ^ 3) - 3 * barY ^ 2 * (∑ i, tail i) +
          ∑ _i : Fin n, 2 * barY ^ 3 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ i, (tail i) ^ 3) - (n : ℝ) * barY ^ 3 := by
          simp [hsum]
          ring

lemma gm_trace3_near_extremal_clustering_lower_envelope_tail_mean {n : ℕ} (hn : 1 ≤ n)
    (S1 x barY : ℝ) (hbar : barY = (S1 - x) / (n : ℝ)) :
    gmTrace3LowerEnvelope (n + 1) S1 x = x ^ 3 + (n : ℝ) * barY ^ 3 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  unfold gmTrace3LowerEnvelope
  have hpred : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by norm_num
  rw [hpred, hbar]
  field_simp [hn0]

def gm_trace3_near_extremal_clustering_statement : Prop :=
  ∀ (n : ℕ) (_hn : 1 ≤ n) (S1 x xstar eps : ℝ) (tail : Fin n → ℝ),
    0 ≤ S1 →
      S1 / ((n + 1 : ℕ) : ℝ) ≤ x →
        x ≤ xstar →
          0 ≤ eps →
            0 < (S1 - x) / (n : ℝ) →
              (∀ i, 0 ≤ tail i) →
                (∑ i, tail i = S1 - x) →
                  x ^ 3 + (∑ i, (tail i) ^ 3) ≤
                      gmTrace3LowerEnvelope (n + 1) S1 xstar →
                    gmTrace3LowerEnvelope (n + 1) S1 xstar -
                        gmTrace3LowerEnvelope (n + 1) S1 x ≤
                      2 * ((S1 - x) / (n : ℝ)) * eps ^ 2 →
                      ∀ i, |tail i - (S1 - x) / (n : ℝ)| ≤ eps

/-- Paper label: `prop:gm-trace3-near-extremal-clustering`. A finite tail spectrum whose
third moment nearly saturates the trace-three lower envelope clusters around its tail mean. -/
theorem paper_gm_trace3_near_extremal_clustering :
    gm_trace3_near_extremal_clustering_statement := by
  intro n hn S1 x xstar eps tail hS1 hx hxx heps hbar_pos htail_nonneg htail_sum
    hmoment henv_gap i
  let barY : ℝ := (S1 - x) / (n : ℝ)
  have _henv_mono :
      gmTrace3LowerEnvelope (n + 1) S1 x ≤ gmTrace3LowerEnvelope (n + 1) S1 xstar :=
    gm_trace3_near_extremal_clustering_lower_envelope_mono hn hS1 hx hxx
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have htail_sum_bar : ∑ i, tail i = (n : ℝ) * barY := by
    rw [htail_sum]
    dsimp [barY]
    field_simp [hn0]
  have henv_x :
      gmTrace3LowerEnvelope (n + 1) S1 x = x ^ 3 + (n : ℝ) * barY ^ 3 :=
    gm_trace3_near_extremal_clustering_lower_envelope_tail_mean hn S1 x barY rfl
  have hsum_identity :
      (∑ j, (tail j - barY) ^ 2 * (tail j + 2 * barY)) =
        (∑ j, (tail j) ^ 3) - (n : ℝ) * barY ^ 3 :=
    gm_trace3_near_extremal_clustering_tail_cube_gap_identity tail barY htail_sum_bar
  have hsummand_nonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (tail j - barY) ^ 2 * (tail j + 2 * barY) := by
    intro j _
    exact mul_nonneg (sq_nonneg _) (by nlinarith [htail_nonneg j, hbar_pos])
  have hterm_le_sum :
      (tail i - barY) ^ 2 * (tail i + 2 * barY) ≤
        ∑ j, (tail j - barY) ^ 2 * (tail j + 2 * barY) := by
    exact Finset.single_le_sum hsummand_nonneg (by simp)
  have hsum_le_env :
      (∑ j, (tail j - barY) ^ 2 * (tail j + 2 * barY)) ≤
        gmTrace3LowerEnvelope (n + 1) S1 xstar - gmTrace3LowerEnvelope (n + 1) S1 x := by
    rw [hsum_identity, henv_x]
    nlinarith [hmoment]
  have hfactor_le :
      2 * barY * (tail i - barY) ^ 2 ≤
        (tail i - barY) ^ 2 * (tail i + 2 * barY) := by
    have hfactor : 2 * barY ≤ tail i + 2 * barY := by nlinarith [htail_nonneg i]
    calc
      2 * barY * (tail i - barY) ^ 2 =
          (tail i - barY) ^ 2 * (2 * barY) := by ring
      _ ≤ (tail i - barY) ^ 2 * (tail i + 2 * barY) :=
          mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
  have hmul_sq :
      2 * barY * (tail i - barY) ^ 2 ≤ 2 * barY * eps ^ 2 := by
    nlinarith [hfactor_le, hterm_le_sum, hsum_le_env, henv_gap]
  have hpos : 0 < 2 * barY := by positivity
  have hsquare : (tail i - barY) ^ 2 ≤ eps ^ 2 :=
    le_of_mul_le_mul_left hmul_sq hpos
  have habs_le : |tail i - barY| ≤ |eps| := (sq_le_sq.mp hsquare)
  simpa [barY, abs_of_nonneg heps] using habs_le

end

end Omega.SyncKernelRealInput
