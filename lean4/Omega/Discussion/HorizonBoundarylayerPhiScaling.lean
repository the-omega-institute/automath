import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Discussion

open scoped goldenRatio

/-- The horizon boundary-layer parameter `ρ_m = tanh((m log φ)/2)`. -/
noncomputable def discussion_horizon_boundarylayer_phi_scaling_rho (m : ℕ) : ℝ :=
  Real.tanh (((m : ℝ) * Real.log Real.goldenRatio) / 2)

/-- The Euclidean boundary-layer thickness `1 - ρ_m²`. -/
noncomputable def discussion_horizon_boundarylayer_phi_scaling_thickness (m : ℕ) : ℝ :=
  1 - discussion_horizon_boundarylayer_phi_scaling_rho m ^ 2

/-- The closed form obtained from `1 - tanh²(x/2) = 2 / (1 + cosh x)` and
`cosh (m log φ) = (φ^m + φ^{-m}) / 2`. -/
def discussion_horizon_boundarylayer_phi_scaling_identity (m : ℕ) : Prop :=
  discussion_horizon_boundarylayer_phi_scaling_thickness m =
      2 / (1 + Real.cosh ((m : ℝ) * Real.log Real.goldenRatio)) ∧
    discussion_horizon_boundarylayer_phi_scaling_thickness m =
      4 / (Real.goldenRatio ^ m + (Real.goldenRatio ^ m)⁻¹ + 2)

/-- A concrete `Θ(φ^{-m})` package: the thickness lies between two constant multiples of
`φ^{-m}`. -/
def discussion_horizon_boundarylayer_phi_scaling_asymptotic (m : ℕ) : Prop :=
  (Real.goldenRatio ^ m)⁻¹ ≤ discussion_horizon_boundarylayer_phi_scaling_thickness m ∧
    discussion_horizon_boundarylayer_phi_scaling_thickness m ≤
      4 * (Real.goldenRatio ^ m)⁻¹

private lemma discussion_horizon_boundarylayer_phi_scaling_phi_pow_pos (m : ℕ) :
    0 < Real.goldenRatio ^ m := by
  positivity

private lemma discussion_horizon_boundarylayer_phi_scaling_phi_pow_ge_one (m : ℕ) :
    1 ≤ Real.goldenRatio ^ m := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        1 ≤ Real.goldenRatio ^ m := hm
        _ ≤ Real.goldenRatio ^ m * Real.goldenRatio := by
              nlinarith [hm, le_of_lt Real.one_lt_goldenRatio]
        _ = Real.goldenRatio ^ (m + 1) := by
              rw [pow_succ]

private lemma discussion_horizon_boundarylayer_phi_scaling_hyperbolic_identity (x : ℝ) :
    1 - Real.tanh (x / 2) ^ 2 = 2 / (1 + Real.cosh x) := by
  have hcosh_pos : 0 < Real.cosh (x / 2) := Real.cosh_pos (x / 2)
  have hcosh_ne : Real.cosh (x / 2) ≠ 0 := ne_of_gt hcosh_pos
  have hbase : 1 - Real.tanh (x / 2) ^ 2 = 1 / Real.cosh (x / 2) ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hcosh_ne]
    nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hden :
      1 + Real.cosh x = 2 * Real.cosh (x / 2) ^ 2 := by
    have hsq : Real.cosh (x / 2) ^ 2 - Real.sinh (x / 2) ^ 2 = 1 :=
      Real.cosh_sq_sub_sinh_sq (x / 2)
    calc
      1 + Real.cosh x = 1 + Real.cosh (2 * (x / 2)) := by ring_nf
      _ = 1 + (Real.cosh (x / 2) ^ 2 + Real.sinh (x / 2) ^ 2) := by
            rw [Real.cosh_two_mul]
      _ = 2 * Real.cosh (x / 2) ^ 2 := by
            nlinarith
  rw [hbase, hden]
  field_simp [hcosh_ne]

private lemma discussion_horizon_boundarylayer_phi_scaling_cosh_closed_form (m : ℕ) :
    Real.cosh ((m : ℝ) * Real.log Real.goldenRatio) =
      (Real.goldenRatio ^ m + (Real.goldenRatio ^ m)⁻¹) / 2 := by
  have hpow_pos : 0 < Real.goldenRatio ^ m :=
    discussion_horizon_boundarylayer_phi_scaling_phi_pow_pos m
  have hlog :
      Real.log (Real.goldenRatio ^ m) = (m : ℝ) * Real.log Real.goldenRatio := by
    calc
      Real.log (Real.goldenRatio ^ m) = Real.log (Real.goldenRatio ^ (m : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (m : ℝ) * Real.log Real.goldenRatio := Real.log_rpow Real.goldenRatio_pos (m : ℝ)
  rw [← hlog, Real.cosh_log hpow_pos]

/-- Paper label: `cor:discussion-horizon-boundarylayer-phi-scaling`. -/
theorem paper_discussion_horizon_boundarylayer_phi_scaling (m : ℕ) :
    discussion_horizon_boundarylayer_phi_scaling_identity m ∧
      discussion_horizon_boundarylayer_phi_scaling_asymptotic m := by
  let a : ℝ := Real.goldenRatio ^ m
  have ha_pos : 0 < a := discussion_horizon_boundarylayer_phi_scaling_phi_pow_pos m
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha_ge_one : 1 ≤ a := discussion_horizon_boundarylayer_phi_scaling_phi_pow_ge_one m
  have hidentity1 :
      discussion_horizon_boundarylayer_phi_scaling_thickness m =
        2 / (1 + Real.cosh ((m : ℝ) * Real.log Real.goldenRatio)) := by
    unfold discussion_horizon_boundarylayer_phi_scaling_thickness
      discussion_horizon_boundarylayer_phi_scaling_rho
    simpa using
      discussion_horizon_boundarylayer_phi_scaling_hyperbolic_identity
        ((m : ℝ) * Real.log Real.goldenRatio)
  have hcosh :
      Real.cosh ((m : ℝ) * Real.log Real.goldenRatio) = (a + a⁻¹) / 2 := by
    simpa [a] using discussion_horizon_boundarylayer_phi_scaling_cosh_closed_form m
  have hidentity2 :
      discussion_horizon_boundarylayer_phi_scaling_thickness m =
        4 / (a + a⁻¹ + 2) := by
    rw [hidentity1, hcosh]
    field_simp [ha_ne]
    ring
  have hInvLeOne : a⁻¹ ≤ 1 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) ha_ge_one)
  have hden_pos : 0 < a + a⁻¹ + 2 := by positivity
  have hden_ge : a ≤ a + a⁻¹ + 2 := by
    have hInvNonneg : 0 ≤ a⁻¹ := by positivity
    nlinarith
  have hden_le : a + a⁻¹ + 2 ≤ 4 * a := by
    nlinarith
  have hupper :
      4 / (a + a⁻¹ + 2) ≤ 4 * a⁻¹ := by
    have hInv :
        (a + a⁻¹ + 2)⁻¹ ≤ a⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le ha_pos hden_ge
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hInv (by positivity : (0 : ℝ) ≤ 4)
  have hlower :
      a⁻¹ ≤ 4 / (a + a⁻¹ + 2) := by
    have hInv :
        (4 * a)⁻¹ ≤ (a + a⁻¹ + 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hden_pos hden_le
    have hmul := mul_le_mul_of_nonneg_left hInv (by positivity : (0 : ℝ) ≤ 4)
    have hfour_ne : (4 : ℝ) ≠ 0 := by norm_num
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ha_ne, hfour_ne] using hmul
  refine ⟨⟨hidentity1, by simpa [a] using hidentity2⟩, ?_⟩
  constructor
  · rw [hidentity2]
    simpa [a] using hlower
  · rw [hidentity2]
    simpa [a] using hupper
