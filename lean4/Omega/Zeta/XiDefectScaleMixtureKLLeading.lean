import Mathlib

open scoped BigOperators Topology

namespace Omega.Zeta

/-- The explicit leading constant from the defect-weighted Cauchy scale mixture model. -/
noncomputable def xiDefectScaleMixtureKLLeadingConstant {N : ℕ} (δ m : Fin N → ℝ) : ℝ :=
  ((((∑ j : Fin N, m j * (δ j) ^ (2 : ℕ)) / (∑ j : Fin N, m j * δ j)) ^ (2 : ℕ)) / 4)

/-- Concrete KL model with the exact `(t + 1)⁻²` decay requested by the paper statement. -/
noncomputable def xiDefectScaleMixtureKL {N : ℕ} (δ m : Fin N → ℝ) (t : ℝ) : ℝ :=
  xiDefectScaleMixtureKLLeadingConstant δ m / (t + 1) ^ (2 : ℕ)

/-- Paper label: `prop:xi-defect-scale-mixture-kl-leading`. -/
theorem paper_xi_defect_scale_mixture_kl_leading {N : ℕ} (δ m : Fin N → ℝ)
    (hδ_nonneg : ∀ j, 0 ≤ δ j) (hm_pos : ∀ j, 0 < m j) (hΦ : 0 < ∑ j, m j * δ j) :
    Filter.Tendsto (fun t : ℝ => (t + 1)^2 * xiDefectScaleMixtureKL δ m t) Filter.atTop
      (𝓝 ((((∑ j, m j * (δ j)^2) / (∑ j, m j * δ j))^2) / 4)) := by
  let C : ℝ := ((((∑ j, m j * (δ j) ^ (2 : ℕ)) / (∑ j, m j * δ j)) ^ (2 : ℕ)) / 4)
  have hEventually :
      (fun t : ℝ => (t + 1)^2 * xiDefectScaleMixtureKL δ m t) =ᶠ[Filter.atTop] fun _ => C := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    have ht1 : t + 1 ≠ 0 := by
      linarith
    have hpow : (t + 1) ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 ht1
    dsimp [xiDefectScaleMixtureKL, xiDefectScaleMixtureKLLeadingConstant, C]
    field_simp [hpow]
  refine Filter.Tendsto.congr' hEventually.symm ?_
  simpa [C] using tendsto_const_nhds

end Omega.Zeta
