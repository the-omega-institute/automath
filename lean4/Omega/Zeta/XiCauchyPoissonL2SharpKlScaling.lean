import Mathlib.Tactic
import Omega.Zeta.XiCauchyPoissonAllLpSharpScaling
import Omega.Zeta.XiPoissonCauchyKlFourthOrderUniversality

namespace Omega.Zeta

noncomputable section

/-- The squared `L²` sharp constant appearing in the Poisson--Cauchy coarse-graining profile. -/
def xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq : ℝ :=
  xi_cauchy_poisson_all_lp_sharp_scaling_l2_sharp_constant ^ 2

/-- The KL-to-`L²` scaling factor predicted by the sharp asymptotics. -/
def xi_cauchy_poisson_l2_sharp_kl_scaling_kl_prefactor : ℝ :=
  2 * Real.pi / 3

/-- Concrete package for the `L²` sharp constant and its compatibility with the universal fourth-
order Poisson--Cauchy KL coefficient. -/
def xi_cauchy_poisson_l2_sharp_kl_scaling_statement : Prop :=
  xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq = 3 / (16 * Real.pi) ∧
    xi_poisson_cauchy_kl_fourth_order_universality_main_term 1 1 = 1 / 8 ∧
    xi_poisson_cauchy_kl_fourth_order_universality_main_term 1 1 =
      xi_cauchy_poisson_l2_sharp_kl_scaling_kl_prefactor *
        xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq

/-- Paper label: `thm:xi-cauchy-poisson-l2-sharp-kl-scaling`.
The verified `L²` sharp constant squares to `3 / (16π)`, the universal fourth-order KL main term
is `1 / 8`, and these constants match through the exact scaling factor `2π / 3`. -/
theorem paper_xi_cauchy_poisson_l2_sharp_kl_scaling :
    xi_cauchy_poisson_l2_sharp_kl_scaling_statement := by
  have hl2 :
      xi_cauchy_poisson_all_lp_sharp_scaling_l2_sharp_constant =
        Real.sqrt 3 / (4 * Real.sqrt Real.pi) := by
    exact paper_xi_cauchy_poisson_all_lp_sharp_scaling.2.2.2
  have hl2sq : xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq = 3 / (16 * Real.pi) := by
    unfold xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq
    rw [hl2, div_pow, mul_pow]
    have h3 : 0 ≤ (3 : ℝ) := by positivity
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    norm_num [pow_two, Real.sq_sqrt h3, Real.sq_sqrt hpi]
  have hkl :
      xi_poisson_cauchy_kl_fourth_order_universality_main_term 1 1 = 1 / 8 := by
    rcases paper_xi_poisson_cauchy_kl_fourth_order_universality 1 0 1 zero_lt_one with
      ⟨_, _, hmain⟩
    simpa using hmain
  have hscale :
      xi_poisson_cauchy_kl_fourth_order_universality_main_term 1 1 =
        xi_cauchy_poisson_l2_sharp_kl_scaling_kl_prefactor *
          xi_cauchy_poisson_l2_sharp_kl_scaling_l2_constant_sq := by
    rw [hkl, hl2sq, xi_cauchy_poisson_l2_sharp_kl_scaling_kl_prefactor]
    field_simp [show Real.pi ≠ 0 by exact ne_of_gt Real.pi_pos]
    ring
  exact ⟨hl2sq, hkl, hscale⟩

end

end Omega.Zeta
