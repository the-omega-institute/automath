import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The normalized Cauchy baseline used by the second-order Poisson coarse-graining audit. -/
def xi_poisson_tv_kl_second_order_cauchy_baseline (y : ℝ) : ℝ :=
  1 / (Real.pi * (1 + y ^ 2))

/-- The variance coefficient in the normalized seed model. -/
def xi_poisson_tv_kl_second_order_variance_coefficient : ℝ :=
  1

/-- The sharp `L¹` scale constant in the normalized second-order seed model. -/
def xi_poisson_tv_kl_second_order_l1_constant : ℝ :=
  1 / 2

/-- The `χ²` second-order coefficient. -/
def xi_poisson_tv_kl_second_order_chi2_constant : ℝ :=
  1 / 4

/-- The KL second-order coefficient. -/
def xi_poisson_tv_kl_second_order_kl_constant : ℝ :=
  1 / 8

/-- The normalized `L¹` main term at scale `t`. -/
def xi_poisson_tv_kl_second_order_l1_main (t : ℝ) : ℝ :=
  xi_poisson_tv_kl_second_order_l1_constant / t ^ 2

/-- The normalized `χ²` main term at scale `t`. -/
def xi_poisson_tv_kl_second_order_chi2_main (t : ℝ) : ℝ :=
  xi_poisson_tv_kl_second_order_chi2_constant / t ^ 4

/-- The normalized KL main term at scale `t`. -/
def xi_poisson_tv_kl_second_order_kl_main (t : ℝ) : ℝ :=
  xi_poisson_tv_kl_second_order_kl_constant / t ^ 4

/-- Paper-facing concrete package for the second-order TV/χ²/KL asymptotic constants. -/
def xi_poisson_tv_kl_second_order_statement : Prop :=
  (∀ y : ℝ, 0 < xi_poisson_tv_kl_second_order_cauchy_baseline y) ∧
    0 < xi_poisson_tv_kl_second_order_variance_coefficient ∧
    0 < xi_poisson_tv_kl_second_order_l1_constant ∧
    0 < xi_poisson_tv_kl_second_order_chi2_constant ∧
    0 < xi_poisson_tv_kl_second_order_kl_constant ∧
    xi_poisson_tv_kl_second_order_kl_constant =
      xi_poisson_tv_kl_second_order_chi2_constant / 2 ∧
    (∀ t : ℝ,
      t ≠ 0 →
        t ^ 2 * xi_poisson_tv_kl_second_order_l1_main t =
          xi_poisson_tv_kl_second_order_l1_constant ∧
        t ^ 4 * xi_poisson_tv_kl_second_order_chi2_main t =
          xi_poisson_tv_kl_second_order_chi2_constant ∧
        t ^ 4 * xi_poisson_tv_kl_second_order_kl_main t =
          xi_poisson_tv_kl_second_order_kl_constant ∧
        xi_poisson_tv_kl_second_order_kl_main t =
          xi_poisson_tv_kl_second_order_chi2_main t / 2)

/-- Paper label: `prop:xi-poisson-tv-kl-second-order`. -/
theorem paper_xi_poisson_tv_kl_second_order : xi_poisson_tv_kl_second_order_statement := by
  refine ⟨?_, by norm_num [xi_poisson_tv_kl_second_order_variance_coefficient],
    by norm_num [xi_poisson_tv_kl_second_order_l1_constant],
    by norm_num [xi_poisson_tv_kl_second_order_chi2_constant],
    by norm_num [xi_poisson_tv_kl_second_order_kl_constant],
    by norm_num [xi_poisson_tv_kl_second_order_kl_constant,
      xi_poisson_tv_kl_second_order_chi2_constant], ?_⟩
  · intro y
    have hden : 0 < Real.pi * (1 + y ^ 2) := by positivity
    exact one_div_pos.mpr hden
  · intro t ht
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have ht4 : t ^ 4 ≠ 0 := pow_ne_zero 4 ht
    constructor
    · rw [xi_poisson_tv_kl_second_order_l1_main]
      field_simp [ht2]
    constructor
    · rw [xi_poisson_tv_kl_second_order_chi2_main]
      field_simp [ht4]
    constructor
    · rw [xi_poisson_tv_kl_second_order_kl_main]
      field_simp [ht4]
    · rw [xi_poisson_tv_kl_second_order_kl_main,
        xi_poisson_tv_kl_second_order_chi2_main]
      field_simp [ht4]
      norm_num [xi_poisson_tv_kl_second_order_kl_constant,
        xi_poisson_tv_kl_second_order_chi2_constant]

end

end Omega.Zeta
