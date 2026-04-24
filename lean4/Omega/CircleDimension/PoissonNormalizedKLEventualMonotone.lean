import Mathlib

namespace Omega.CircleDimension

/-- Paper label: `cor:cdim-poisson-normalized-kl-eventual-monotone`. -/
theorem paper_cdim_poisson_normalized_kl_eventual_monotone
    (A A' : ℝ → ℝ) (sigma c : ℝ) (hCoeff : c < 0)
    (hA : Filter.Tendsto (fun t => t^2 * (A t - sigma^4 / 8)) Filter.atTop (nhds c))
    (hA' : Filter.Tendsto (fun t => t^3 * A' t) Filter.atTop (nhds (-2 * c))) :
    ∃ t0, ∀ t ≥ t0, A t < sigma^4 / 8 ∧ 0 < A' t := by
  have hc_half_neg : c / 2 < 0 := by
    linarith
  have hprod_eventually :
      ∀ᶠ t in Filter.atTop, t^2 * (A t - sigma^4 / 8) < c / 2 := by
    exact hA.eventually (Iio_mem_nhds (by linarith : c < c / 2))
  have hderiv_eventually :
      ∀ᶠ t in Filter.atTop, -c < t^3 * A' t := by
    have hlt : -c < -2 * c := by
      linarith
    exact hA'.eventually (Ioi_mem_nhds hlt)
  have hlarge_eventually : ∀ᶠ t : ℝ in Filter.atTop, 1 ≤ t := by
    exact Filter.eventually_ge_atTop 1
  have hgoal_eventually : ∀ᶠ t : ℝ in Filter.atTop, A t < sigma^4 / 8 ∧ 0 < A' t := by
    filter_upwards [hprod_eventually, hderiv_eventually, hlarge_eventually] with t hprod hderiv ht
    have ht2_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
    have ht3_nonneg : 0 ≤ t ^ 3 := by positivity
    have hA_lt : A t < sigma^4 / 8 := by
      by_contra hnot
      have hA_nonneg : 0 ≤ A t - sigma^4 / 8 := by linarith
      have hprod_nonneg : 0 ≤ t ^ 2 * (A t - sigma^4 / 8) := by
        exact mul_nonneg ht2_nonneg hA_nonneg
      linarith
    have hscaled_pos : 0 < t ^ 3 * A' t := by
      linarith
    have hA'_pos : 0 < A' t := by
      by_contra hnot
      have hA'_nonpos : A' t ≤ 0 := by linarith
      have hscaled_nonpos : t ^ 3 * A' t ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos ht3_nonneg hA'_nonpos
      linarith
    exact ⟨hA_lt, hA'_pos⟩
  rcases Filter.eventually_atTop.1 hgoal_eventually with ⟨t0, ht0⟩
  exact ⟨t0, fun t ht => ht0 t ht⟩

end Omega.CircleDimension
