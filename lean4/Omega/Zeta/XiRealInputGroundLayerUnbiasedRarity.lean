import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Topology

/-- Paper label: `thm:xi-real-input-ground-layer-unbiased-rarity`. -/
theorem paper_xi_real_input_ground_layer_unbiased_rarity
    (c : ℝ) (A Z p T : ℕ → ℝ) (hc : 1 < c) (hp : ∀ n, p n = A n / Z n)
    (hT : ∀ n, T n = (p n)⁻¹)
    (hA :
      Filter.Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log c)))
    (hZ :
      Filter.Tendsto (fun n : ℕ => Real.log (Z n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log (Real.goldenRatio ^ (2 : ℕ))))) :
    Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log c - Real.log (Real.goldenRatio ^ (2 : ℕ)))) ∧
      Filter.Tendsto (fun n : ℕ => Real.log (T n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log (Real.goldenRatio ^ (2 : ℕ)) - Real.log c)) := by
  have hlogc_pos : 0 < Real.log c := Real.log_pos hc
  have hphi_sq_gt_one : 1 < Real.goldenRatio ^ (2 : ℕ) := by
    have hphi_gt_one : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
    rw [pow_two]
    have hprod_pos : 0 < (Real.goldenRatio - 1) * (Real.goldenRatio + 1) := by
      exact mul_pos (sub_pos.mpr hphi_gt_one) (by linarith)
    nlinarith
  have hlogphi_pos : 0 < Real.log (Real.goldenRatio ^ (2 : ℕ)) :=
    Real.log_pos hphi_sq_gt_one
  have hA_eventually :
      ∀ᶠ n in atTop, 0 < Real.log (A n) / (n : ℝ) :=
    hA.eventually (Ioi_mem_nhds hlogc_pos)
  have hZ_eventually :
      ∀ᶠ n in atTop, 0 < Real.log (Z n) / (n : ℝ) :=
    hZ.eventually (Ioi_mem_nhds hlogphi_pos)
  have hbase_eventually :
      ∀ᶠ n in atTop, 0 < n ∧ 0 < Real.log (A n) ∧ 0 < Real.log (Z n) := by
    filter_upwards [eventually_gt_atTop 0, hA_eventually, hZ_eventually] with n hn hAn hZn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlogA_pos : 0 < Real.log (A n) := by
      rwa [div_pos_iff_of_pos_right hn_pos] at hAn
    have hlogZ_pos : 0 < Real.log (Z n) := by
      rwa [div_pos_iff_of_pos_right hn_pos] at hZn
    exact ⟨hn, hlogA_pos, hlogZ_pos⟩
  have hp_rate :
      Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log c - Real.log (Real.goldenRatio ^ (2 : ℕ)))) := by
    refine (hA.sub hZ).congr' ?_
    filter_upwards [hbase_eventually] with n hn
    rcases hn with ⟨_, hlogA_pos, hlogZ_pos⟩
    have hA_ne : A n ≠ 0 := by
      intro hzero
      rw [hzero, Real.log_zero] at hlogA_pos
      exact (lt_irrefl (0 : ℝ)) hlogA_pos
    have hZ_ne : Z n ≠ 0 := by
      intro hzero
      rw [hzero, Real.log_zero] at hlogZ_pos
      exact (lt_irrefl (0 : ℝ)) hlogZ_pos
    exact
      (calc
        Real.log (p n) / (n : ℝ) = Real.log (A n / Z n) / (n : ℝ) := by rw [hp n]
        _ = (Real.log (A n) - Real.log (Z n)) / (n : ℝ) := by
          rw [Real.log_div hA_ne hZ_ne]
        _ = Real.log (A n) / (n : ℝ) - Real.log (Z n) / (n : ℝ) := by
          ring).symm
  have hT_rate :
      Filter.Tendsto (fun n : ℕ => Real.log (T n) / (n : ℝ)) Filter.atTop
        (𝓝 (Real.log (Real.goldenRatio ^ (2 : ℕ)) - Real.log c)) := by
    refine (hZ.sub hA).congr' ?_
    filter_upwards [hbase_eventually] with n hn
    rcases hn with ⟨_, hlogA_pos, hlogZ_pos⟩
    have hA_ne : A n ≠ 0 := by
      intro hzero
      rw [hzero, Real.log_zero] at hlogA_pos
      exact (lt_irrefl (0 : ℝ)) hlogA_pos
    have hZ_ne : Z n ≠ 0 := by
      intro hzero
      rw [hzero, Real.log_zero] at hlogZ_pos
      exact (lt_irrefl (0 : ℝ)) hlogZ_pos
    exact
      (calc
        Real.log (T n) / (n : ℝ) = Real.log ((p n)⁻¹) / (n : ℝ) := by rw [hT n]
        _ = -(Real.log (p n)) / (n : ℝ) := by rw [Real.log_inv]
        _ = -(Real.log (A n / Z n)) / (n : ℝ) := by rw [hp n]
        _ = -(Real.log (A n) - Real.log (Z n)) / (n : ℝ) := by
          rw [Real.log_div hA_ne hZ_ne]
        _ = Real.log (Z n) / (n : ℝ) - Real.log (A n) / (n : ℝ) := by
          ring).symm
  exact ⟨hp_rate, hT_rate⟩

end Omega.Zeta
