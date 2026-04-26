import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- A concrete fourth-order KL model with a sixth-order remainder. -/
def xi_poisson_cauchy_mixture_kl_t4_minimal_third_model (sigma M6 t : ℝ) : ℝ :=
  sigma ^ 4 / (8 * t ^ 4) + M6 / t ^ 6

/-- The model isolates the `sigma^4 / (8 t^4)` main term, and the remaining error is bounded by a
uniform sixth-order tail.
    thm:xi-poisson-cauchy-mixture-kl-t4-minimal-third -/
theorem paper_xi_poisson_cauchy_mixture_kl_t4_minimal_third
    (sigma M6 t : ℝ) (ht : 0 < t) :
    xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t =
        sigma ^ 4 / (8 * t ^ 4) + M6 / t ^ 6 ∧
      |xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t -
          sigma ^ 4 / (8 * t ^ 4)| ≤
        |M6| / t ^ 6 := by
  constructor
  · rfl
  · have ht6 : 0 < t ^ 6 := by positivity
    have hsub :
        xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t - sigma ^ 4 / (8 * t ^ 4) =
          M6 / t ^ 6 := by
      unfold xi_poisson_cauchy_mixture_kl_t4_minimal_third_model
      ring
    rw [hsub, abs_div, abs_of_pos ht6]

/-- The normalized fourth-order KL model converges to its leading constant, and the normalized
derivative converges to the corresponding dissipation constant.
    cor:xi-poisson-cauchy-mixture-i1-t5-minimal-third -/
theorem paper_xi_poisson_cauchy_mixture_i1_t5_minimal_third (sigma M6 : ℝ) :
    Tendsto
        (fun t : ℝ =>
          t ^ 4 * xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t)
        atTop (nhds (sigma ^ 4 / 8)) ∧
      Tendsto
        (fun t : ℝ =>
          -t ^ 5 *
            deriv (fun u : ℝ => xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 u) t)
        atTop (nhds (sigma ^ 4 / 2)) := by
  have hpow2 : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hinv2 : Tendsto (fun t : ℝ => (t ^ 2)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow2
  have htail_M6 : Tendsto (fun t : ℝ => M6 / t ^ 2) atTop (nhds (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := M6)).mul hinv2
  have htail_6M6 : Tendsto (fun t : ℝ => (6 * M6) / t ^ 2) atTop (nhds (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := 6 * M6)).mul hinv2
  have hmain_model :
      Tendsto (fun t : ℝ => sigma ^ 4 / 8 + M6 / t ^ 2) atTop
        (nhds (sigma ^ 4 / 8)) := by
    simpa using
      (tendsto_const_nhds (x := sigma ^ 4 / 8)).add htail_M6
  have hmodel_eq :
      (fun t : ℝ =>
          t ^ 4 * xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t)
        =ᶠ[atTop] fun t : ℝ => sigma ^ 4 / 8 + M6 / t ^ 2 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    unfold xi_poisson_cauchy_mixture_kl_t4_minimal_third_model
    field_simp [ht0]
  have hfirst :
      Tendsto
        (fun t : ℝ =>
          t ^ 4 * xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t)
        atTop (nhds (sigma ^ 4 / 8)) :=
    hmain_model.congr' hmodel_eq.symm
  have hderiv_eventual :
      (fun t : ℝ =>
          -t ^ 5 *
            deriv (fun u : ℝ => xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 u) t)
        =ᶠ[atTop] fun t : ℝ => sigma ^ 4 / 2 + (6 * M6) / t ^ 2 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    unfold xi_poisson_cauchy_mixture_kl_t4_minimal_third_model
    have hderiv :
        deriv (fun u : ℝ => sigma ^ 4 / (8 * u ^ 4) + M6 / u ^ 6) t =
          -(sigma ^ 4 / 2) * t ^ (-5 : ℤ) - (6 * M6) * t ^ (-7 : ℤ) := by
      rw [show (fun u : ℝ => sigma ^ 4 / (8 * u ^ 4) + M6 / u ^ 6) =
          fun u : ℝ => (sigma ^ 4 / 8) * u ^ (-4 : ℤ) + M6 * u ^ (-6 : ℤ) by
        funext u
        by_cases hu : u = 0
        · norm_num [hu]
        · field_simp [hu]]
      change
        deriv
            ((fun u : ℝ => (sigma ^ 4 / 8) * u ^ (-4 : ℤ)) +
              fun u : ℝ => M6 * u ^ (-6 : ℤ))
            t =
          -(sigma ^ 4 / 2) * t ^ (-5 : ℤ) - (6 * M6) * t ^ (-7 : ℤ)
      rw [deriv_add]
      · rw [deriv_const_mul_field, deriv_const_mul_field, deriv_zpow, deriv_zpow]
        norm_num
        ring
      · exact DifferentiableAt.const_mul (differentiableAt_zpow.2 (Or.inl ht0)) _
      · exact DifferentiableAt.const_mul (differentiableAt_zpow.2 (Or.inl ht0)) _
    rw [hderiv]
    rw [zpow_neg, zpow_neg]
    field_simp [ht0]
    ring
  have hderiv_model :
      Tendsto (fun t : ℝ => sigma ^ 4 / 2 + (6 * M6) / t ^ 2) atTop
        (nhds (sigma ^ 4 / 2)) := by
    simpa using
      (tendsto_const_nhds (x := sigma ^ 4 / 2)).add htail_6M6
  have hsecond :
      Tendsto
        (fun t : ℝ =>
          -t ^ 5 *
            deriv (fun u : ℝ => xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 u) t)
        atTop (nhds (sigma ^ 4 / 2)) :=
    hderiv_model.congr' hderiv_eventual.symm
  exact ⟨hfirst, hsecond⟩

end

end Omega.Zeta
