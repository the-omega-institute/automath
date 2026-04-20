import Mathlib

namespace Omega.Zeta

/-- Paper label: `cor:finite-part-near-rh-q-axis-envelope`. -/
theorem paper_etds_finite_part_near_rh_q_axis_envelope
    (Psi : ℕ → ℝ) (rootRate spectralRadius : ℝ) (kernelRH : Prop)
    (hKernelRH : kernelRH ↔ spectralRadius ≤ rootRate)
    (hUpper : spectralRadius ≤ rootRate → ∃ K > 0, ∀ q, |Psi q| ≤ K * rootRate ^ q)
    (hLower : rootRate < spectralRadius →
      ∃ c > 0, ∀ N, ∃ q ≥ N, c * spectralRadius ^ q ≤ |Psi q|) :
    (kernelRH ↔ ∃ K > 0, ∀ q, |Psi q| ≤ K * rootRate ^ q) ∧
      (¬ kernelRH → ∃ c > 0, ∀ N, ∃ q ≥ N, c * spectralRadius ^ q ≤ |Psi q|) := by
  constructor
  · constructor
    · intro hk
      exact hUpper ((hKernelRH.mp hk))
    · rintro ⟨K, hK_pos, hK⟩
      by_contra hk
      have hroot_lt_spectral : rootRate < spectralRadius := by
        exact lt_of_not_ge ((not_congr hKernelRH).mp hk)
      rcases hLower hroot_lt_spectral with ⟨c, hc_pos, hc⟩
      have hroot_nonneg : 0 ≤ rootRate := by
        have hbound := hK 1
        have habs_nonneg : 0 ≤ |Psi 1| := abs_nonneg (Psi 1)
        nlinarith
      have hspectral_pos : 0 < spectralRadius := by
        linarith
      set r : ℝ := rootRate / spectralRadius
      have hr_nonneg : 0 ≤ r := by
        exact div_nonneg hroot_nonneg hspectral_pos.le
      have hr_lt_one : r < 1 := by
        rw [show r = rootRate / spectralRadius by rfl]
        exact (div_lt_one hspectral_pos).2 hroot_lt_spectral
      have hpow_zero : Filter.Tendsto (fun q : ℕ => r ^ q) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr_nonneg hr_lt_one
      have hratio_eventually : ∀ᶠ q : ℕ in Filter.atTop, r ^ q < c / K := by
        have hratio_pos : 0 < c / K := by
          exact div_pos hc_pos hK_pos
        exact hpow_zero.eventually (Iio_mem_nhds hratio_pos)
      rcases Filter.eventually_atTop.1 hratio_eventually with ⟨N, hN⟩
      rcases hc N with ⟨q, hqN, hqLower⟩
      have hratio_small : r ^ q < c / K := hN q hqN
      have hKratio_lt : K * r ^ q < c := by
        have hmul := mul_lt_mul_of_pos_left hratio_small hK_pos
        calc
          K * r ^ q < K * (c / K) := by simpa [mul_assoc] using hmul
          _ = c := by field_simp [hK_pos.ne']
      have hroot_eq : rootRate = spectralRadius * r := by
        rw [show r = rootRate / spectralRadius by rfl]
        field_simp [hspectral_pos.ne']
      have hupper_q : |Psi q| ≤ (K * r ^ q) * spectralRadius ^ q := by
        calc
          |Psi q| ≤ K * rootRate ^ q := hK q
          _ = K * ((spectralRadius * r) ^ q) := by rw [hroot_eq]
          _ = K * (spectralRadius ^ q * r ^ q) := by rw [mul_pow]
          _ = (K * r ^ q) * spectralRadius ^ q := by ring
      have hcompare : (K * r ^ q) * spectralRadius ^ q < c * spectralRadius ^ q := by
        exact mul_lt_mul_of_pos_right hKratio_lt (pow_pos hspectral_pos q)
      linarith
  · intro hk
    exact hLower (lt_of_not_ge ((not_congr hKernelRH).mp hk))

end Omega.Zeta
