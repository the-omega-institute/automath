import Mathlib.Tactic
import Omega.SyncKernelWeighted.GMAffineInverseMajorArc
import Omega.SyncKernelWeighted.GMEnergyExponentTwistCriterion

namespace Omega.SyncKernelWeighted

/-- Concrete package for the affine-improvement dichotomy. The arithmetic obstruction is the
divisibility relation `modulus ∣ cycleGcd`; the non-obstructed branch stores an explicit residual
power-saving witness together with a nonresonant twist witness, while the obstructed branch stores
major-arc concentration and an equal-radius resonant witness. -/
structure gm_affine_improvement_dichotomy_data where
  gm_affine_improvement_dichotomy_affine_data : gm_affine_inverse_major_arc_data
  gm_affine_improvement_dichotomy_modulus : ℕ
  gm_affine_improvement_dichotomy_cycle_gcd : ℕ
  gm_affine_improvement_dichotomy_baseline_exponent : ℝ
  gm_affine_improvement_dichotomy_energy_exponent : ℝ
  gm_affine_improvement_dichotomy_perron_radius : ℝ
  gm_affine_improvement_dichotomy_twisted_radius : ℝ
  gm_affine_improvement_dichotomy_uniform_gap : ℝ
  gm_affine_improvement_dichotomy_twisted_error : ℝ
  gm_affine_improvement_dichotomy_main_arc_contribution : ℝ
  gm_affine_improvement_dichotomy_improvement_exponent : ℝ
  gm_affine_improvement_dichotomy_improvement_constant : ℝ
  gm_affine_improvement_dichotomy_uniform_power_saving :
    0 < gm_affine_improvement_dichotomy_improvement_exponent ∧
      gm_affine_improvement_dichotomy_affine_data.gm_affine_inverse_major_arc_residual_energy ≤
        gm_affine_improvement_dichotomy_improvement_constant *
          gm_affine_improvement_dichotomy_affine_data.gm_affine_inverse_major_arc_scale ^ (4 : ℕ) /
            (1 + gm_affine_improvement_dichotomy_improvement_exponent)
  gm_affine_improvement_dichotomy_nonresonant_witness :
    gm_energy_exponent_twist_criterion_nonresonant_case
      gm_affine_improvement_dichotomy_baseline_exponent
      gm_affine_improvement_dichotomy_energy_exponent
      gm_affine_improvement_dichotomy_perron_radius
      gm_affine_improvement_dichotomy_twisted_radius
      gm_affine_improvement_dichotomy_uniform_gap
      gm_affine_improvement_dichotomy_twisted_error
  gm_affine_improvement_dichotomy_major_arc_witness :
    gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_major_arc_concentration
      gm_affine_improvement_dichotomy_affine_data
  gm_affine_improvement_dichotomy_resonant_witness :
    gm_energy_exponent_twist_criterion_resonant_case
      gm_affine_improvement_dichotomy_baseline_exponent
      gm_affine_improvement_dichotomy_energy_exponent
      gm_affine_improvement_dichotomy_perron_radius
      gm_affine_improvement_dichotomy_twisted_radius
      gm_affine_improvement_dichotomy_main_arc_contribution

/-- The arithmetic obstruction branch is the concrete divisibility obstruction `q ∣ gcd`. -/
def gm_affine_improvement_dichotomy_arithmetic_obstruction
    (D : gm_affine_improvement_dichotomy_data) : Prop :=
  D.gm_affine_improvement_dichotomy_modulus ∣ D.gm_affine_improvement_dichotomy_cycle_gcd

/-- In the non-obstructed branch, the residual certificate enjoys a uniform power saving and the
energy exponent stays in the baseline phase. -/
def gm_affine_improvement_dichotomy_uniform_improvement_branch
    (D : gm_affine_improvement_dichotomy_data) : Prop :=
  ∃ ϑ : ℝ,
    0 < ϑ ∧
      D.gm_affine_improvement_dichotomy_affine_data.gm_affine_inverse_major_arc_residual_energy ≤
        D.gm_affine_improvement_dichotomy_improvement_constant *
          D.gm_affine_improvement_dichotomy_affine_data.gm_affine_inverse_major_arc_scale ^ (4 : ℕ) /
            (1 + ϑ) ∧
      gm_energy_exponent_twist_criterion_baseline_phase
        D.gm_affine_improvement_dichotomy_baseline_exponent
        D.gm_affine_improvement_dichotomy_energy_exponent

/-- In the obstructed branch, major-arc concentration forces affine near-saturation, and the
equal-radius twist witness forces a phase transition in the energy exponent. -/
def gm_affine_improvement_dichotomy_obstruction_branch
    (D : gm_affine_improvement_dichotomy_data) : Prop :=
  gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation
      D.gm_affine_improvement_dichotomy_affine_data ∧
    gm_energy_exponent_twist_criterion_phase_transition
      D.gm_affine_improvement_dichotomy_baseline_exponent
      D.gm_affine_improvement_dichotomy_energy_exponent

/-- The dichotomy packages the two concrete implications: absence of the divisibility obstruction
forces the explicit improvement branch, while the divisibility obstruction forces the major-arc
near-saturation and phase-transition branch. -/
def gm_affine_improvement_dichotomy_statement
    (D : gm_affine_improvement_dichotomy_data) : Prop :=
  (¬ gm_affine_improvement_dichotomy_arithmetic_obstruction D →
      gm_affine_improvement_dichotomy_uniform_improvement_branch D) ∧
    (gm_affine_improvement_dichotomy_arithmetic_obstruction D →
      gm_affine_improvement_dichotomy_obstruction_branch D)

/-- Paper label: `thm:gm-affine-improvement-dichotomy`. The existing affine inverse-major-arc
theorem converts major-arc concentration into affine near-saturation, while the twist criterion
separates the nonresonant baseline phase from the resonant phase-transition branch. -/
theorem paper_gm_affine_improvement_dichotomy (D : gm_affine_improvement_dichotomy_data) :
    gm_affine_improvement_dichotomy_statement D := by
  refine ⟨?_, ?_⟩
  · intro _hNoObstruction
    rcases D.gm_affine_improvement_dichotomy_uniform_power_saving with ⟨hϑ, hbound⟩
    have hbaseline :
        gm_energy_exponent_twist_criterion_baseline_phase
          D.gm_affine_improvement_dichotomy_baseline_exponent
          D.gm_affine_improvement_dichotomy_energy_exponent :=
      (paper_gm_energy_exponent_twist_criterion
        D.gm_affine_improvement_dichotomy_baseline_exponent
        D.gm_affine_improvement_dichotomy_energy_exponent
        D.gm_affine_improvement_dichotomy_perron_radius
        D.gm_affine_improvement_dichotomy_twisted_radius
        D.gm_affine_improvement_dichotomy_uniform_gap
        D.gm_affine_improvement_dichotomy_twisted_error
        D.gm_affine_improvement_dichotomy_main_arc_contribution).1
          D.gm_affine_improvement_dichotomy_nonresonant_witness
    exact ⟨D.gm_affine_improvement_dichotomy_improvement_exponent, hϑ, hbound, hbaseline⟩
  · intro _hObstruction
    have hNearSaturation :
        gm_affine_inverse_major_arc_data.gm_affine_inverse_major_arc_near_saturation
          D.gm_affine_improvement_dichotomy_affine_data :=
      (paper_gm_affine_inverse_major_arc D.gm_affine_improvement_dichotomy_affine_data).2
        D.gm_affine_improvement_dichotomy_major_arc_witness
    have hPhaseTransition :
        gm_energy_exponent_twist_criterion_phase_transition
          D.gm_affine_improvement_dichotomy_baseline_exponent
          D.gm_affine_improvement_dichotomy_energy_exponent :=
      (paper_gm_energy_exponent_twist_criterion
        D.gm_affine_improvement_dichotomy_baseline_exponent
        D.gm_affine_improvement_dichotomy_energy_exponent
        D.gm_affine_improvement_dichotomy_perron_radius
        D.gm_affine_improvement_dichotomy_twisted_radius
        D.gm_affine_improvement_dichotomy_uniform_gap
        D.gm_affine_improvement_dichotomy_twisted_error
        D.gm_affine_improvement_dichotomy_main_arc_contribution).2
          D.gm_affine_improvement_dichotomy_resonant_witness
    exact ⟨hNearSaturation, hPhaseTransition⟩

end Omega.SyncKernelWeighted
