import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The golden-ratio endpoint `φ`. -/
noncomputable def xi_real_input_40_collision_minimal_modulus_two_witness_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The cubic whose largest real root is the mod-`2` Perron root proxy. -/
def xi_real_input_40_collision_minimal_modulus_two_witness_poly (x : ℝ) : ℝ :=
  x ^ (3 : ℕ) - 2 * x ^ (2 : ℕ) - 1

/-- The ambient growth rate `λ = φ²`. -/
noncomputable def xi_real_input_40_collision_minimal_modulus_two_witness_lambda : ℝ :=
  xi_real_input_40_collision_minimal_modulus_two_witness_phi ^ (2 : ℕ)

/-- The logarithmic exponent attached to a real root `ρ`. -/
noncomputable def xi_real_input_40_collision_minimal_modulus_two_witness_theta (ρ : ℝ) : ℝ :=
  Real.log ρ / Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda

/-- The minimal nontrivial twist modulus predicate used in the paper discussion. -/
def xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist (m : ℕ) : Prop :=
  2 ≤ m

/-- Paper-facing statement: there is a real root `ρ` of `x^3 - 2x^2 - 1` in the interval
`(φ, 1 + √2)`, the associated logarithmic exponent lies strictly between `1/2` and `1`, and
modulus `2` is the minimal modulus carrying a nontrivial twist. -/
def xi_real_input_40_collision_minimal_modulus_two_witness_statement : Prop :=
  ∃ ρ : ℝ,
    xi_real_input_40_collision_minimal_modulus_two_witness_poly ρ = 0 ∧
      xi_real_input_40_collision_minimal_modulus_two_witness_phi < ρ ∧
      ρ < 1 + Real.sqrt 2 ∧
      (1 : ℝ) / 2 <
        xi_real_input_40_collision_minimal_modulus_two_witness_theta ρ ∧
      xi_real_input_40_collision_minimal_modulus_two_witness_theta ρ <
        Real.log (1 + Real.sqrt 2) /
          Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda ∧
      Real.log (1 + Real.sqrt 2) /
          Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda <
        1 ∧
      xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist 2 ∧
      ∀ m < 2, ¬ xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist m

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_sqrt5_sq :
    (Real.sqrt 5) ^ (2 : ℕ) = 5 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq :
    (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_phi_sq :
    xi_real_input_40_collision_minimal_modulus_two_witness_phi ^ (2 : ℕ) =
      xi_real_input_40_collision_minimal_modulus_two_witness_phi + 1 := by
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_phi
  nlinarith [xi_real_input_40_collision_minimal_modulus_two_witness_sqrt5_sq]

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_phi_pos :
    0 < xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_phi
  positivity

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_phi_gt_one :
    1 < xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
  have hsqrt5_gt_one : 1 < Real.sqrt 5 := by
    have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := by positivity
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_phi
  nlinarith

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_phi_lt_one_add_sqrt_two :
    xi_real_input_40_collision_minimal_modulus_two_witness_phi < 1 + Real.sqrt 2 := by
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_phi
  have hsqrt5_sq := xi_real_input_40_collision_minimal_modulus_two_witness_sqrt5_sq
  have hsqrt2_sq := xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq
  have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := by positivity
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := by positivity
  nlinarith

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_phi_eval :
    xi_real_input_40_collision_minimal_modulus_two_witness_poly
        xi_real_input_40_collision_minimal_modulus_two_witness_phi =
      -2 := by
  have hphi_sq := xi_real_input_40_collision_minimal_modulus_two_witness_phi_sq
  have hphi_cube :
      xi_real_input_40_collision_minimal_modulus_two_witness_phi ^ (3 : ℕ) =
        2 * xi_real_input_40_collision_minimal_modulus_two_witness_phi + 1 := by
    calc
      xi_real_input_40_collision_minimal_modulus_two_witness_phi ^ (3 : ℕ) =
          xi_real_input_40_collision_minimal_modulus_two_witness_phi *
            xi_real_input_40_collision_minimal_modulus_two_witness_phi ^ (2 : ℕ) := by
              ring
      _ =
          xi_real_input_40_collision_minimal_modulus_two_witness_phi *
            (xi_real_input_40_collision_minimal_modulus_two_witness_phi + 1) := by
              rw [hphi_sq]
      _ = 2 * xi_real_input_40_collision_minimal_modulus_two_witness_phi + 1 := by
              nlinarith
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_poly
  rw [hphi_cube, hphi_sq]
  ring

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_upper_sq :
    (1 + Real.sqrt 2) ^ (2 : ℕ) = 3 + 2 * Real.sqrt 2 := by
  nlinarith [xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq]

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_upper_cube :
    (1 + Real.sqrt 2) ^ (3 : ℕ) = 7 + 5 * Real.sqrt 2 := by
  calc
    (1 + Real.sqrt 2) ^ (3 : ℕ) = (1 + Real.sqrt 2) * (1 + Real.sqrt 2) ^ (2 : ℕ) := by
      ring
    _ = (1 + Real.sqrt 2) * (3 + 2 * Real.sqrt 2) := by
      rw [xi_real_input_40_collision_minimal_modulus_two_witness_upper_sq]
    _ = 7 + 5 * Real.sqrt 2 := by
      nlinarith [xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq]

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_upper_eval :
    xi_real_input_40_collision_minimal_modulus_two_witness_poly (1 + Real.sqrt 2) =
      Real.sqrt 2 := by
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_poly
  rw [xi_real_input_40_collision_minimal_modulus_two_witness_upper_cube,
    xi_real_input_40_collision_minimal_modulus_two_witness_upper_sq]
  ring

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_lambda_eq :
    xi_real_input_40_collision_minimal_modulus_two_witness_lambda =
      xi_real_input_40_collision_minimal_modulus_two_witness_phi + 1 := by
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_lambda
  exact xi_real_input_40_collision_minimal_modulus_two_witness_phi_sq

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_lambda_gt_one_add_sqrt_two :
    1 + Real.sqrt 2 <
      xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
  rw [xi_real_input_40_collision_minimal_modulus_two_witness_lambda_eq]
  have hsqrt2_sq := xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := by positivity
  have hphi_gt_sqrt2 :
      Real.sqrt 2 <
        xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
    have hphi_sq := xi_real_input_40_collision_minimal_modulus_two_witness_phi_sq
    have hphi_pos := xi_real_input_40_collision_minimal_modulus_two_witness_phi_pos
    have hphi_gt_one := xi_real_input_40_collision_minimal_modulus_two_witness_phi_gt_one
    nlinarith [xi_real_input_40_collision_minimal_modulus_two_witness_sqrt2_sq]
  linarith

private lemma xi_real_input_40_collision_minimal_modulus_two_witness_lambda_gt_one :
    1 < xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by positivity)
  have hone : (1 : ℝ) < 1 + Real.sqrt 2 := by linarith
  exact lt_trans hone
    xi_real_input_40_collision_minimal_modulus_two_witness_lambda_gt_one_add_sqrt_two

/-- Paper label: `thm:xi-real-input-40-collision-minimal-modulus-two-witness`. -/
theorem paper_xi_real_input_40_collision_minimal_modulus_two_witness :
    xi_real_input_40_collision_minimal_modulus_two_witness_statement := by
  have hcont : Continuous xi_real_input_40_collision_minimal_modulus_two_witness_poly := by
    unfold xi_real_input_40_collision_minimal_modulus_two_witness_poly
    continuity
  have hφu :
      xi_real_input_40_collision_minimal_modulus_two_witness_phi < 1 + Real.sqrt 2 := by
    exact xi_real_input_40_collision_minimal_modulus_two_witness_phi_lt_one_add_sqrt_two
  have hφeval :
      xi_real_input_40_collision_minimal_modulus_two_witness_poly
          xi_real_input_40_collision_minimal_modulus_two_witness_phi =
        -2 := by
    exact xi_real_input_40_collision_minimal_modulus_two_witness_phi_eval
  have hu_eval :
      xi_real_input_40_collision_minimal_modulus_two_witness_poly (1 + Real.sqrt 2) =
        Real.sqrt 2 := by
    exact xi_real_input_40_collision_minimal_modulus_two_witness_upper_eval
  have hzero_mem :
      (0 : ℝ) ∈ Set.Ioo
        (xi_real_input_40_collision_minimal_modulus_two_witness_poly
          xi_real_input_40_collision_minimal_modulus_two_witness_phi)
        (xi_real_input_40_collision_minimal_modulus_two_witness_poly (1 + Real.sqrt 2)) := by
    rw [hφeval, hu_eval]
    constructor
    · norm_num
    · exact Real.sqrt_pos.2 (by positivity)
  rcases intermediate_value_Ioo
      (show
        xi_real_input_40_collision_minimal_modulus_two_witness_phi ≤ 1 + Real.sqrt 2 by linarith)
      hcont.continuousOn hzero_mem with ⟨ρ, hρmem, hρroot⟩
  have hρ_gt : xi_real_input_40_collision_minimal_modulus_two_witness_phi < ρ := hρmem.1
  have hρ_lt : ρ < 1 + Real.sqrt 2 := hρmem.2
  have hρ_pos : 0 < ρ := lt_trans xi_real_input_40_collision_minimal_modulus_two_witness_phi_pos hρ_gt
  have hloglam_pos :
      0 < Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
    have hlam_gt_one :
        1 < xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
      exact xi_real_input_40_collision_minimal_modulus_two_witness_lambda_gt_one
    exact Real.log_pos hlam_gt_one
  have htheta_upper :
      xi_real_input_40_collision_minimal_modulus_two_witness_theta ρ <
        Real.log (1 + Real.sqrt 2) /
          Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
    unfold xi_real_input_40_collision_minimal_modulus_two_witness_theta
    have hlog_upper : Real.log ρ < Real.log (1 + Real.sqrt 2) := by
      exact Real.log_lt_log hρ_pos hρ_lt
    exact (div_lt_div_iff_of_pos_right hloglam_pos).2 hlog_upper
  have hφ_pos : 0 < xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
    exact xi_real_input_40_collision_minimal_modulus_two_witness_phi_pos
  have hlogφ_pos :
      0 < Real.log xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
    exact Real.log_pos xi_real_input_40_collision_minimal_modulus_two_witness_phi_gt_one
  have htheta_lower :
      (1 : ℝ) / 2 < xi_real_input_40_collision_minimal_modulus_two_witness_theta ρ := by
    have hlog_lt :
        Real.log xi_real_input_40_collision_minimal_modulus_two_witness_phi < Real.log ρ :=
      Real.log_lt_log hφ_pos hρ_gt
    have hlog_lambda :
        Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda =
          2 * Real.log xi_real_input_40_collision_minimal_modulus_two_witness_phi := by
      unfold xi_real_input_40_collision_minimal_modulus_two_witness_lambda
      rw [pow_two, Real.log_mul hφ_pos.ne' hφ_pos.ne']
      ring
    unfold xi_real_input_40_collision_minimal_modulus_two_witness_theta
    refine (lt_div_iff₀ hloglam_pos).2 ?_
    rw [hlog_lambda]
    nlinarith
  have hlog_upper_lt :
      Real.log (1 + Real.sqrt 2) /
          Real.log xi_real_input_40_collision_minimal_modulus_two_witness_lambda <
        1 := by
    refine (div_lt_iff₀ hloglam_pos).2 ?_
    have hupper_lt_lambda :
        1 + Real.sqrt 2 <
          xi_real_input_40_collision_minimal_modulus_two_witness_lambda := by
      exact xi_real_input_40_collision_minimal_modulus_two_witness_lambda_gt_one_add_sqrt_two
    have hupper_pos : 0 < 1 + Real.sqrt 2 := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by positivity)
      linarith
    simpa using Real.log_lt_log hupper_pos hupper_lt_lambda
  refine ⟨ρ, hρroot, hρ_gt, hρ_lt, htheta_lower, htheta_upper, hlog_upper_lt, ?_, ?_⟩
  · show xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist 2
    unfold xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist
    omega
  intro m hm
  unfold xi_real_input_40_collision_minimal_modulus_two_witness_has_nontrivial_twist
  omega

end

end Omega.Zeta
