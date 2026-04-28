import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete asymptotic data for the Cauchy--Poisson KL expansion on golden scales. -/
structure xi_cauchy_poisson_kl_golden_scale_data where
  xi_cauchy_poisson_kl_golden_scale_klAtScale : ℝ → ℝ
  xi_cauchy_poisson_kl_golden_scale_remainderAtScale : ℝ → ℝ
  xi_cauchy_poisson_kl_golden_scale_sigma : ℝ
  xi_cauchy_poisson_kl_golden_scale_mu3 : ℝ
  xi_cauchy_poisson_kl_golden_scale_mu4 : ℝ
  xi_cauchy_poisson_kl_golden_scale_sharpExpansion :
    ∀ t : ℝ,
      t ≠ 0 →
        xi_cauchy_poisson_kl_golden_scale_klAtScale t =
          (xi_cauchy_poisson_kl_golden_scale_sigma ^ 4 / 8) / t ^ 4 +
            (3 * xi_cauchy_poisson_kl_golden_scale_mu3 ^ 2 / 32 -
                xi_cauchy_poisson_kl_golden_scale_sigma ^ 2 *
                  xi_cauchy_poisson_kl_golden_scale_mu4 / 8 +
                xi_cauchy_poisson_kl_golden_scale_sigma ^ 6 / 64) / t ^ 6 +
              xi_cauchy_poisson_kl_golden_scale_remainderAtScale t / t ^ 8

namespace xi_cauchy_poisson_kl_golden_scale_data

/-- The coefficient of the `phi^{-2m}` correction after fourth-order renormalization. -/
def correctionCoefficient (D : xi_cauchy_poisson_kl_golden_scale_data) : ℝ :=
  3 * D.xi_cauchy_poisson_kl_golden_scale_mu3 ^ 2 / 32 -
    D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 2 *
      D.xi_cauchy_poisson_kl_golden_scale_mu4 / 8 +
      D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 6 / 64

/-- The fourth-order renormalized expansion along `t_m = phi^m`. -/
def goldenScaleRenormalizedExpansion
    (D : xi_cauchy_poisson_kl_golden_scale_data) : Prop :=
  ∀ m : ℕ,
    (Real.goldenRatio ^ m) ^ 4 *
        D.xi_cauchy_poisson_kl_golden_scale_klAtScale (Real.goldenRatio ^ m) =
      D.xi_cauchy_poisson_kl_golden_scale_sigma ^ 4 / 8 +
        ((Real.goldenRatio ^ m) ^ 2)⁻¹ * D.correctionCoefficient +
          ((Real.goldenRatio ^ m) ^ 4)⁻¹ *
            D.xi_cauchy_poisson_kl_golden_scale_remainderAtScale (Real.goldenRatio ^ m)

end xi_cauchy_poisson_kl_golden_scale_data

/-- Paper label: `cor:xi-cauchy-poisson-kl-golden-scale`. -/
theorem paper_xi_cauchy_poisson_kl_golden_scale
    (h : xi_cauchy_poisson_kl_golden_scale_data) :
    h.goldenScaleRenormalizedExpansion := by
  rw [xi_cauchy_poisson_kl_golden_scale_data.goldenScaleRenormalizedExpansion]
  intro m
  have hphi : Real.goldenRatio ≠ 0 := ne_of_gt Real.goldenRatio_pos
  have ht : Real.goldenRatio ^ m ≠ 0 := pow_ne_zero m hphi
  rw [h.xi_cauchy_poisson_kl_golden_scale_sharpExpansion (Real.goldenRatio ^ m) ht,
    xi_cauchy_poisson_kl_golden_scale_data.correctionCoefficient]
  field_simp [ht, pow_ne_zero 2 ht, pow_ne_zero 4 ht, pow_ne_zero 6 ht, pow_ne_zero 8 ht]

end

end Omega.Zeta
