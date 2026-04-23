import Mathlib
import Omega.Zeta.AbelDampingSemigroupDissipation
import Omega.Zeta.AbelPowerbaseCovariancePolePowerMap

namespace Omega.Zeta

noncomputable section

/-- The critical damping threshold used in the concrete bifurcation package. -/
def xi_abel_damping_threshold_bifurcation_delta_c : ℝ := 0

/-- Test vector concentrating all Hardy energy in the first nontrivial mode. -/
def xi_abel_damping_threshold_bifurcation_test_vector : Fin 2 → ℝ :=
  ![0, 1]

/-- Damped Hardy energy of the concrete test vector. -/
def xi_abel_damping_threshold_bifurcation_energy (δ : ℝ) : ℝ :=
  abel_damping_semigroup_dissipation_energy 2 δ
    xi_abel_damping_threshold_bifurcation_test_vector

lemma xi_abel_damping_threshold_bifurcation_energy_formula (δ : ℝ) :
    xi_abel_damping_threshold_bifurcation_energy δ = Real.exp (-(2 * δ * Real.log 2)) := by
  simp [xi_abel_damping_threshold_bifurcation_energy,
    xi_abel_damping_threshold_bifurcation_test_vector,
    abel_damping_semigroup_dissipation_energy, abel_damping_semigroup_dissipation_weight,
    Fin.sum_univ_two]

lemma xi_abel_damping_threshold_bifurcation_energy_zero :
    xi_abel_damping_threshold_bifurcation_energy 0 = 1 := by
  rw [xi_abel_damping_threshold_bifurcation_energy_formula]
  simp

/-- Concrete threshold package: nonnegative damping is energy-stable, negative damping is
energy-unstable, and the reciprocal pole radius contracts under `b ↦ b²`. -/
def xi_abel_damping_threshold_bifurcation_statement : Prop :=
  xi_abel_damping_threshold_bifurcation_delta_c = 0 ∧
    (∀ δ : ℝ, xi_abel_damping_threshold_bifurcation_delta_c ≤ δ →
      xi_abel_damping_threshold_bifurcation_energy δ ≤
        xi_abel_damping_threshold_bifurcation_energy 0) ∧
    (∀ δ : ℝ, δ < xi_abel_damping_threshold_bifurcation_delta_c →
      xi_abel_damping_threshold_bifurcation_energy 0 <
        xi_abel_damping_threshold_bifurcation_energy δ) ∧
    xiAbelPoleMap (2 ^ 2) 1 1 = (xiAbelPoleMap 2 1 1) ^ 2 ∧
    ((1 : ℚ) / xiAbelPoleMap (2 ^ 2) 1 1) = (((1 : ℚ) / xiAbelPoleMap 2 1 1) ^ 2) ∧
    ((1 : ℚ) / xiAbelPoleMap (2 ^ 2) 1 1) < (1 : ℚ) / xiAbelPoleMap 2 1 1

/-- Paper label: `thm:xi-abel-damping-threshold-bifurcation`. -/
theorem paper_xi_abel_damping_threshold_bifurcation :
    xi_abel_damping_threshold_bifurcation_statement := by
  have hpower :=
    paper_xi_abel_powerbase_covariance_pole_power_map
      (ψ := fun n => n) (h := fun n => n) (b := 2) (m := 2) (ρ := 1) (δ := 1)
  refine ⟨rfl, ?_, ?_, hpower.2.2.2, ?_, ?_⟩
  · intro δ hδ
    exact
      (paper_abel_damping_semigroup_dissipation (m := 2) (b := 2) (hb := by norm_num)
        (δ₁ := δ) (δ₂ := 0) (δ := δ) hδ
        xi_abel_damping_threshold_bifurcation_test_vector).2.1
  · intro δ hδ
    rw [xi_abel_damping_threshold_bifurcation_delta_c] at hδ
    rw [xi_abel_damping_threshold_bifurcation_energy_zero,
      xi_abel_damping_threshold_bifurcation_energy_formula]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : 0 < -(2 * δ * Real.log 2) := by
      nlinarith
    simpa using Real.one_lt_exp_iff.mpr harg
  · norm_num [xiAbelPoleMap]
  · norm_num [xiAbelPoleMap]

end

end Omega.Zeta
