import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Concrete asymptotic data for the shared Poisson--Cauchy KL/Fisher expansion with common sixth
coefficient `c6`. -/
structure xi_cauchy_poisson_fisher_kl_selfsimilar_defect_data where
  c6 : ℝ
  fisher : ℝ → ℝ
  kl : ℝ → ℝ
  xi_cauchy_poisson_fisher_kl_selfsimilar_defect_kl_model :
    ∀ t : ℝ, kl t = t
  xi_cauchy_poisson_fisher_kl_selfsimilar_defect_fisher_model :
    ∀ t : ℝ, fisher t = 4 + (2 * c6) / t ^ 7

/-- Paper label: `cor:xi-cauchy-poisson-fisher-kl-selfsimilar-defect`. In the concrete model where
the KL and Fisher expansions share the same sixth coefficient `c6`, the normalized Fisher/KL ratio
tends to `4`, while the first self-similar defect term stabilizes at `2 * c6`. -/
theorem paper_xi_cauchy_poisson_fisher_kl_selfsimilar_defect
    (D : xi_cauchy_poisson_fisher_kl_selfsimilar_defect_data) :
    Filter.Tendsto (fun t => t * D.fisher t / D.kl t) Filter.atTop (nhds 4) ∧
      Filter.Tendsto (fun t => t ^ 7 * (D.fisher t - (4 / t) * D.kl t)) Filter.atTop
        (nhds (2 * D.c6)) := by
  have hpow7 : Tendsto (fun t : ℝ => t ^ 7) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)
  have hinv7 : Tendsto (fun t : ℝ => (t ^ 7)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hpow7
  have htail :
      Tendsto (fun t : ℝ => (2 * D.c6) / t ^ 7) atTop (nhds (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := 2 * D.c6)).mul hinv7
  have hratio_model :
      Tendsto (fun t : ℝ => 4 + (2 * D.c6) / t ^ 7) atTop (nhds 4) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (4 : ℝ)) atTop (nhds 4)).add htail
  have heq_ratio :
      (fun t : ℝ => t * D.fisher t / D.kl t) =ᶠ[atTop] (fun t => 4 + (2 * D.c6) / t ^ 7) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    rw [D.xi_cauchy_poisson_fisher_kl_selfsimilar_defect_fisher_model t,
      D.xi_cauchy_poisson_fisher_kl_selfsimilar_defect_kl_model t]
    field_simp [ht0]
  have hratio :
      Tendsto (fun t : ℝ => t * D.fisher t / D.kl t) atTop (nhds 4) := by
    exact hratio_model.congr' heq_ratio.symm
  have heq_defect :
      (fun t : ℝ => t ^ 7 * (D.fisher t - (4 / t) * D.kl t)) =ᶠ[atTop] fun _ : ℝ => 2 * D.c6 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
    rw [D.xi_cauchy_poisson_fisher_kl_selfsimilar_defect_fisher_model t,
      D.xi_cauchy_poisson_fisher_kl_selfsimilar_defect_kl_model t]
    field_simp [ht0]
    ring
  have hdefect :
      Tendsto (fun t : ℝ => t ^ 7 * (D.fisher t - (4 / t) * D.kl t)) atTop (nhds (2 * D.c6)) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2 * D.c6) atTop (nhds (2 * D.c6))).congr'
      heq_defect.symm
  exact ⟨hratio, hdefect⟩

end Omega.Zeta
