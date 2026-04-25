import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped BigOperators

/-- Paper label: `thm:conclusion-tqft-high-genus-bottom-spectrum-peeling`. -/
theorem paper_conclusion_tqft_high_genus_bottom_spectrum_peeling {s : ℕ}
    (δ μ : Fin s → ℕ) (hδ_pos : ∀ j, 0 < δ j) (hδ_strict : StrictMono δ) :
    ∀ r : Fin s,
      Filter.Tendsto
        (fun g : ℕ =>
          (μ r : ℝ) +
            ∑ j : {j : Fin s // r < j},
              (μ (j : Fin s) : ℝ) *
                (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ (2 * g - 2)))
        Filter.atTop (nhds (μ r : ℝ)) := by
  intro r
  have hsum_zero :
      Filter.Tendsto
        (fun g : ℕ =>
          ∑ j : {j : Fin s // r < j},
            (μ (j : Fin s) : ℝ) *
              (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ (2 * g - 2)))
        Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ _j : {j : Fin s // r < j}, (0 : ℝ) by simp]
    refine tendsto_finset_sum Finset.univ ?_
    intro j _hj
    have hδj_pos_nat : 0 < δ (j : Fin s) := hδ_pos (j : Fin s)
    have hδ_lt_nat : δ r < δ (j : Fin s) := hδ_strict j.property
    have hratio_nonneg : 0 ≤ (δ r : ℝ) / (δ (j : Fin s) : ℝ) := by
      positivity
    have hratio_lt_one : (δ r : ℝ) / (δ (j : Fin s) : ℝ) < 1 := by
      rw [div_lt_one]
      · exact_mod_cast hδ_lt_nat
      · exact_mod_cast hδj_pos_nat
    have hpow_even :
        Filter.Tendsto
          (fun g : ℕ => (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ (2 * g)))
          Filter.atTop (nhds 0) := by
      have hsq_lt : ((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ 2 < 1 := by
        nlinarith [mul_self_nonneg ((δ r : ℝ) / (δ (j : Fin s) : ℝ))]
      have hsq_tendsto :
          Filter.Tendsto
            (fun g : ℕ => (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ 2) ^ g)
            Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hsq_lt
      simpa [pow_mul] using hsq_tendsto
    have htail :
        Filter.Tendsto
          (fun g : ℕ => (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ (2 * g - 2)))
          Filter.atTop (nhds 0) := by
      have hsq_lt : ((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ 2 < 1 := by
        nlinarith [mul_self_nonneg ((δ r : ℝ) / (δ (j : Fin s) : ℝ))]
      have hsq_tendsto :
          Filter.Tendsto
            (fun g : ℕ => (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ 2) ^ g)
            Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hsq_lt
      have hshift := hsq_tendsto.comp (tendsto_sub_atTop_nat 1)
      convert hshift using 1
      ext g
      simp only [Function.comp_apply]
      rw [show 2 * g - 2 = 2 * (g - 1) by omega, pow_mul]
    simpa using htail.const_mul (μ (j : Fin s) : ℝ)
  have hconst : Filter.Tendsto (fun _g : ℕ => (μ r : ℝ)) Filter.atTop (nhds (μ r : ℝ)) :=
    tendsto_const_nhds
  simpa using hconst.add hsum_zero

end Omega.Conclusion
