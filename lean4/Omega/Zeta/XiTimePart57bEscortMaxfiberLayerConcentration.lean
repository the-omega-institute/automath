import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter

noncomputable section

/-- The explicit critical order in the audited two-layer model. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_a_c : ℕ := 1

/-- The audited escort order, chosen above the critical threshold. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_a : ℕ := 2

/-- The number `K_m` of maximizing fibers. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_K (_m : ℕ) : ℝ := 1

/-- The total layer size `|X_m|`. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_X (_m : ℕ) : ℝ := 2

/-- The maximal fiber multiplicity `M_m`. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_M (m : ℕ) : ℝ := (2 : ℝ) ^ m

/-- The maximal multiplicity on the complement. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_M2 (_m : ℕ) : ℝ := 1

/-- The leading maximal-fiber contribution `K_m M_m^a`. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_lead (m : ℕ) : ℝ :=
  xi_time_part57b_escort_maxfiber_layer_concentration_K m *
    (xi_time_part57b_escort_maxfiber_layer_concentration_M m) ^
      xi_time_part57b_escort_maxfiber_layer_concentration_a

/-- The complement contribution. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_remainder (m : ℕ) : ℝ :=
  (xi_time_part57b_escort_maxfiber_layer_concentration_X m -
      xi_time_part57b_escort_maxfiber_layer_concentration_K m) *
    (xi_time_part57b_escort_maxfiber_layer_concentration_M2 m) ^
      xi_time_part57b_escort_maxfiber_layer_concentration_a

/-- The full escort sum `S_a(m)`. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_S (m : ℕ) : ℝ :=
  xi_time_part57b_escort_maxfiber_layer_concentration_lead m +
    xi_time_part57b_escort_maxfiber_layer_concentration_remainder m

/-- The normalized complement/lead ratio. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_ratio (m : ℕ) : ℝ :=
  xi_time_part57b_escort_maxfiber_layer_concentration_remainder m /
    xi_time_part57b_escort_maxfiber_layer_concentration_lead m

/-- Paper-facing concentration statement for the explicit two-layer escort model. -/
def xi_time_part57b_escort_maxfiber_layer_concentration_statement : Prop :=
  xi_time_part57b_escort_maxfiber_layer_concentration_a_c <
      xi_time_part57b_escort_maxfiber_layer_concentration_a ∧
    (∀ m : ℕ,
      xi_time_part57b_escort_maxfiber_layer_concentration_S m =
          xi_time_part57b_escort_maxfiber_layer_concentration_lead m +
            xi_time_part57b_escort_maxfiber_layer_concentration_remainder m ∧
        xi_time_part57b_escort_maxfiber_layer_concentration_remainder m ≤
          (xi_time_part57b_escort_maxfiber_layer_concentration_X m -
              xi_time_part57b_escort_maxfiber_layer_concentration_K m) *
            (xi_time_part57b_escort_maxfiber_layer_concentration_M2 m) ^
              xi_time_part57b_escort_maxfiber_layer_concentration_a ∧
        xi_time_part57b_escort_maxfiber_layer_concentration_ratio m =
          xi_time_part57b_escort_maxfiber_layer_concentration_remainder m /
            xi_time_part57b_escort_maxfiber_layer_concentration_lead m ∧
        xi_time_part57b_escort_maxfiber_layer_concentration_ratio m =
          ((1 / 4 : ℝ) ^ m)) ∧
    Tendsto xi_time_part57b_escort_maxfiber_layer_concentration_ratio atTop (nhds 0)

/-- Paper label: `thm:xi-time-part57b-escort-maxfiber-layer-concentration`. In the explicit
two-layer model `S_a(m) = K_m M_m^a + R_m` with `K_m = 1`, `|X_m| = 2`, `M_m = 2^m`,
`M_m^(2) = 1`, and `a = 2 > a_c = 1`, the complement ratio is exactly `(1/4)^m`, so the
finite-layer escort error decays geometrically to `0`. -/
theorem paper_xi_time_part57b_escort_maxfiber_layer_concentration :
    xi_time_part57b_escort_maxfiber_layer_concentration_statement := by
  refine ⟨by decide, ?_, ?_⟩
  · intro m
    have hpow :
        ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
      calc
        ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
        _ = (2 : ℝ) ^ (2 * m) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ 2) ^ m := by rw [← pow_mul]
        _ = (4 : ℝ) ^ m := by norm_num
    refine ⟨rfl, le_rfl, rfl, ?_⟩
    rw [xi_time_part57b_escort_maxfiber_layer_concentration_ratio,
      xi_time_part57b_escort_maxfiber_layer_concentration_remainder,
      xi_time_part57b_escort_maxfiber_layer_concentration_lead,
      xi_time_part57b_escort_maxfiber_layer_concentration_K,
      xi_time_part57b_escort_maxfiber_layer_concentration_X,
      xi_time_part57b_escort_maxfiber_layer_concentration_M,
      xi_time_part57b_escort_maxfiber_layer_concentration_M2,
      xi_time_part57b_escort_maxfiber_layer_concentration_a]
    simp
    rw [hpow]
    norm_num
  · have hratio :
        ∀ m : ℕ,
          xi_time_part57b_escort_maxfiber_layer_concentration_ratio m = ((1 / 4 : ℝ) ^ m) := by
      intro m
      have hpow :
          ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
        calc
          ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
          _ = (2 : ℝ) ^ (2 * m) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ 2) ^ m := by rw [← pow_mul]
          _ = (4 : ℝ) ^ m := by norm_num
      rw [xi_time_part57b_escort_maxfiber_layer_concentration_ratio,
        xi_time_part57b_escort_maxfiber_layer_concentration_remainder,
        xi_time_part57b_escort_maxfiber_layer_concentration_lead,
        xi_time_part57b_escort_maxfiber_layer_concentration_K,
        xi_time_part57b_escort_maxfiber_layer_concentration_X,
        xi_time_part57b_escort_maxfiber_layer_concentration_M,
        xi_time_part57b_escort_maxfiber_layer_concentration_M2,
        xi_time_part57b_escort_maxfiber_layer_concentration_a]
      simp
      rw [hpow]
      norm_num
    have hfun :
        xi_time_part57b_escort_maxfiber_layer_concentration_ratio =
          fun m : ℕ => ((1 / 4 : ℝ) ^ m) := by
      funext m
      exact hratio m
    simpa [hfun] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (by norm_num : (1 / 4 : ℝ) < 1))

end

end Omega.Zeta
