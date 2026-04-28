import Mathlib

namespace Omega.Zeta

open Filter

/-- Paper label: `thm:xi-time-part70-logcm-richardson-residual-ratio`. -/
theorem paper_xi_time_part70_logcm_richardson_residual_ratio
    (q : ℝ) (R : ℕ) (a : ℝ) (res err : ℕ → ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (ha : a ≠ 0)
    (hres :
      ∀ᶠ m in Filter.atTop,
        res m = a * q ^ ((2 * R + 1) * m) * (1 + err m))
    (herr : Filter.Tendsto err Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => res (m + 1) / res m) Filter.atTop
      (nhds (q ^ (2 * R + 1))) := by
  set k : ℕ := 2 * R + 1
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hshift :
      Tendsto (fun m : ℕ => err (m + 1)) atTop (nhds 0) :=
    herr.comp (tendsto_add_atTop_nat 1)
  have hnum :
      Tendsto (fun m : ℕ => 1 + err (m + 1)) atTop (nhds (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add hshift
  have hden :
      Tendsto (fun m : ℕ => 1 + err m) atTop (nhds (1 + 0 : ℝ)) :=
    tendsto_const_nhds.add herr
  have hquot :
      Tendsto (fun m : ℕ => (1 + err (m + 1)) / (1 + err m)) atTop
        (nhds ((1 + 0 : ℝ) / (1 + 0 : ℝ))) :=
    hnum.div hden (by norm_num)
  have hmodel :
      (fun m : ℕ => res (m + 1) / res m) =ᶠ[atTop]
        fun m : ℕ => q ^ k * ((1 + err (m + 1)) / (1 + err m)) := by
    have hres_succ :
        ∀ᶠ m in atTop,
          res (m + 1) = a * q ^ (k * (m + 1)) * (1 + err (m + 1)) := by
      simpa [k] using (tendsto_add_atTop_nat 1).eventually hres
    have herr_ne :
        ∀ᶠ m in atTop, 1 + err m ≠ 0 := by
      have hsmall : ∀ᶠ m in atTop, err m ∈ Set.Ioo (-(1 : ℝ) / 2) (1 / 2) :=
        herr.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
      filter_upwards [hsmall] with m hm
      linarith [hm.1]
    filter_upwards [hres, hres_succ, herr_ne] with m hm hm_succ hm_ne
    have hpow_ne : q ^ (k * m) ≠ 0 := pow_ne_zero _ hq_ne
    calc
      res (m + 1) / res m
          = (a * q ^ (k * (m + 1)) * (1 + err (m + 1))) /
              (a * q ^ (k * m) * (1 + err m)) := by rw [hm_succ, hm]
      _ = q ^ k * ((1 + err (m + 1)) / (1 + err m)) := by
        have hk_succ : k * (m + 1) = k * m + k := by
          rw [Nat.mul_succ]
        rw [hk_succ, pow_add]
        field_simp [ha, hq_ne, hpow_ne, hm_ne]
  refine (tendsto_congr' hmodel).2 ?_
  simpa using (tendsto_const_nhds (x := q ^ k)).mul hquot

end Omega.Zeta
