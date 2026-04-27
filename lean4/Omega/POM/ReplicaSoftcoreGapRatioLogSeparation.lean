import Mathlib

namespace Omega.POM

open Filter

/-- Paper label: `thm:pom-replica-softcore-gap-ratio-log-separation`. -/
theorem paper_pom_replica_softcore_gap_ratio_log_separation
    (rho nu : ℕ → ℝ) (phi : ℝ) (hphi0 : 0 < phi) (hphi2 : phi < 2)
    (hrho_pos : ∀ q, 0 < rho q) (hnu_pos : ∀ q, 0 < nu q)
    (hrho : Tendsto (fun q : ℕ => rho q / (2 : ℝ) ^ q) atTop (nhds (1 / 2)))
    (hnu : Tendsto (fun q : ℕ => nu q / (phi ^ q / 2)) atTop (nhds 1)) :
    Tendsto (fun q : ℕ => (nu q / rho q) / ((phi / 2) ^ q)) atTop (nhds 1) ∧
      Tendsto (fun q : ℕ => Real.log (rho q / nu q) / q) atTop
        (nhds (Real.log (2 / phi))) := by
  have hphi_ne : phi ≠ 0 := ne_of_gt hphi0
  have hphi_div_two_pos : 0 < phi / 2 := by positivity
  have htwo_ne : (2 : ℝ) ≠ 0 := ne_of_gt (lt_trans hphi0 hphi2)
  have hhalf_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hquot :
      Tendsto
        (fun q : ℕ => (nu q / (phi ^ q / 2)) / (rho q / (2 : ℝ) ^ q))
        atTop (nhds (1 / (1 / 2))) := by
    exact hnu.div hrho hhalf_ne
  have hratio_raw :
      Tendsto
        (fun q : ℕ => ((nu q / rho q) / ((phi / 2) ^ q)) * 2)
        atTop (nhds (1 / (1 / 2))) := by
    refine hquot.congr' (Filter.Eventually.of_forall ?_)
    intro q
    have hphi_pow_ne : phi ^ q ≠ 0 := pow_ne_zero q hphi_ne
    have htwo_pow_ne : (2 : ℝ) ^ q ≠ 0 := pow_ne_zero q htwo_ne
    field_simp [ne_of_gt (hrho_pos q), ne_of_gt (hnu_pos q), hphi_pow_ne, htwo_pow_ne,
      htwo_ne]
    calc
      2 ^ q * (phi / 2) ^ q = (2 * (phi / 2)) ^ q := by rw [← mul_pow]
      _ = phi ^ q := by
          congr 1
          ring
  have hratio :
      Tendsto (fun q : ℕ => (nu q / rho q) / ((phi / 2) ^ q)) atTop (nhds 1) := by
    have hscaled := hratio_raw.const_mul ((1 : ℝ) / 2)
    simpa using hscaled.congr' (Filter.Eventually.of_forall fun q => by ring)
  have hlog_ratio :
      Tendsto (fun q : ℕ => Real.log ((nu q / rho q) / ((phi / 2) ^ q))) atTop
        (nhds 0) := by
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    simpa using hlog
  have hlog_ratio_over_q :
      Tendsto
        (fun q : ℕ => Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ))
        atTop (nhds 0) := by
    have hprod :=
      hlog_ratio.mul (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa [div_eq_mul_inv] using hprod
  have hneg_log_ratio_over_q :
      Tendsto
        (fun q : ℕ => -(Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ)))
        atTop (nhds 0) := by
    simpa using hlog_ratio_over_q.neg
  have hconst :
      Tendsto (fun _ : ℕ => Real.log (2 / phi)) atTop (nhds (Real.log (2 / phi))) :=
    tendsto_const_nhds
  have hlog_target_aux :
      Tendsto
        (fun q : ℕ =>
          -(Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ)) + Real.log (2 / phi))
        atTop (nhds (0 + Real.log (2 / phi))) :=
    hneg_log_ratio_over_q.add hconst
  have hlog_target :
      Tendsto (fun q : ℕ => Real.log (rho q / nu q) / (q : ℝ)) atTop
        (nhds (Real.log (2 / phi))) := by
    have hevent :
        (fun q : ℕ =>
          -(Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ)) +
            Real.log (2 / phi)) =ᶠ[atTop]
          (fun q : ℕ => Real.log (rho q / nu q) / (q : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with q hq
      symm
      have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hnu_ne : nu q ≠ 0 := ne_of_gt (hnu_pos q)
      have hrho_ne : rho q ≠ 0 := ne_of_gt (hrho_pos q)
      have hbase_pow_pos : 0 < (phi / 2) ^ q := by positivity
      have hbase_pow_ne : (phi / 2) ^ q ≠ 0 := ne_of_gt hbase_pow_pos
      have hnu_div_rho_pos : 0 < nu q / rho q := div_pos (hnu_pos q) (hrho_pos q)
      have hratio_pos : 0 < (nu q / rho q) / ((phi / 2) ^ q) :=
        div_pos hnu_div_rho_pos hbase_pow_pos
      have hratio_ne : (nu q / rho q) / ((phi / 2) ^ q) ≠ 0 := ne_of_gt hratio_pos
      have hlog_base :
          Real.log ((phi / 2) ^ q) = (q : ℝ) * Real.log (phi / 2) := by
        rw [← Real.rpow_natCast, Real.log_rpow hphi_div_two_pos]
      have hlog_phi_div :
          -Real.log (phi / 2) = Real.log (2 / phi) := by
        rw [Real.log_div htwo_ne hphi_ne, Real.log_div hphi_ne htwo_ne]
        ring
      calc
        Real.log (rho q / nu q) / (q : ℝ)
            = -(Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ)) -
                Real.log (phi / 2) := by
              have hmul :
                  ((nu q / rho q) / ((phi / 2) ^ q)) * ((phi / 2) ^ q) =
                    nu q / rho q := by
                field_simp [hbase_pow_ne]
              have hlog_inv :
                  Real.log (rho q / nu q) = -Real.log (nu q / rho q) := by
                rw [← Real.log_inv]
                congr 1
                field_simp [hnu_ne, hrho_ne]
              have hlog_mul :
                  Real.log (nu q / rho q) =
                    Real.log ((nu q / rho q) / ((phi / 2) ^ q)) +
                      Real.log ((phi / 2) ^ q) := by
                rw [← Real.log_mul hratio_ne hbase_pow_ne, hmul]
              rw [hlog_inv, hlog_mul, hlog_base]
              field_simp [hq_ne]
              ring
        _ = -(Real.log ((nu q / rho q) / ((phi / 2) ^ q)) / (q : ℝ)) +
              Real.log (2 / phi) := by
              rw [← hlog_phi_div]
              ring
    have h := hlog_target_aux.congr' hevent
    simpa using h
  exact ⟨hratio, hlog_target⟩

end Omega.POM
