import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.DerivedTwoTermLaurentSingularRing

namespace Omega.CircleDimension

noncomputable section

/-- The Laurent double-frequency map `z ↦ (z^p + z^q)/2`. -/
abbrev cdim_laurent_double_frequency_critical_value_circle_map (p q : ℕ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (z ^ p + z ^ q)

/-- Its derivative, written via the existing two-term Laurent derivative wrapper. -/
abbrev cdim_laurent_double_frequency_critical_value_circle_derivative
    (p q : ℕ) (z : ℂ) : ℂ :=
  Omega.UnitCirclePhaseArithmetic.twoTermLaurentDerivative (1 / 2 : ℂ) (1 / 2 : ℂ) p q z

/-- Radius of the critical-point circle obtained from `|z|^(p-q) = q/p`. -/
noncomputable def cdim_laurent_double_frequency_critical_value_circle_critical_point_radius
    (p q : ℕ) : ℝ :=
  ((q : ℝ) / (p : ℝ)) ^ ((1 : ℝ) / (p - q : ℝ))

/-- Common modulus of the critical values. -/
noncomputable def cdim_laurent_double_frequency_critical_value_circle_critical_value_radius
    (p q : ℕ) : ℝ :=
  ((p - q : ℝ) / (2 * p : ℝ)) *
    cdim_laurent_double_frequency_critical_value_circle_critical_point_radius p q ^ q

/-- Local branch-radius proxy: in this finite package we record it as the critical-value radius. -/
noncomputable def cdim_laurent_double_frequency_critical_value_circle_branch_radius
    (p q : ℕ) : ℝ :=
  cdim_laurent_double_frequency_critical_value_circle_critical_value_radius p q

/-- Concrete package for the Laurent double-frequency critical equation, the critical-value
modulus formula on the critical circle, and the recorded branch-radius value. -/
def cdim_laurent_double_frequency_critical_value_circle_statement (p q : ℕ) : Prop :=
  (∀ z : ℂ,
      z ≠ 0 →
        (cdim_laurent_double_frequency_critical_value_circle_derivative p q z = 0 ↔
          z ^ (p - q) = -((q : ℂ) / (p : ℂ)))) ∧
    (∀ z : ℂ,
      z ≠ 0 →
        cdim_laurent_double_frequency_critical_value_circle_derivative p q z = 0 →
          cdim_laurent_double_frequency_critical_value_circle_map p q z =
            ((p - q : ℂ) / (2 * p : ℂ)) * z ^ q) ∧
    cdim_laurent_double_frequency_critical_value_circle_branch_radius p q =
      cdim_laurent_double_frequency_critical_value_circle_critical_value_radius p q

theorem cdim_laurent_double_frequency_critical_value_circle_critical_equation
    (p q : ℕ) (hq : 1 ≤ q) (hpq : q < p) (z : ℂ) (hz : z ≠ 0) :
    cdim_laurent_double_frequency_critical_value_circle_derivative p q z = 0 ↔
      z ^ (p - q) = -((q : ℂ) / (p : ℂ)) := by
  have hp0_nat : p ≠ 0 := by omega
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp0_nat
  have hsing :=
    Omega.UnitCirclePhaseArithmetic.paper_derived_two_term_laurent_singular_ring
      (1 / 2 : ℂ) (1 / 2 : ℂ) z p q hz (by norm_num) (by norm_num) hq hpq
  constructor
  · intro hderiv
    have hcrit :
        z ^ (p - q) =
          Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio (1 / 2 : ℂ) (1 / 2 : ℂ)
            p q :=
      (hsing.mp hderiv).1
    have hratio :
        Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
            (1 / 2 : ℂ) (1 / 2 : ℂ) p q =
          -((q : ℂ) / (p : ℂ)) := by
      unfold Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
      field_simp [hp0]
    rw [hratio] at hcrit
    exact hcrit
  · intro hcrit
    have hratio :
        Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
            (1 / 2 : ℂ) (1 / 2 : ℂ) p q =
          -((q : ℂ) / (p : ℂ)) := by
      unfold Omega.UnitCirclePhaseArithmetic.twoTermLaurentCriticalRatio
      field_simp [hp0]
    apply hsing.mpr
    refine ⟨?_, ?_⟩
    · rw [hratio]
      exact hcrit
    · rw [hratio]
      simpa [Complex.norm_pow] using congrArg norm hcrit

theorem cdim_laurent_double_frequency_critical_value_circle_value_formula
    (p q : ℕ) (hq : 1 ≤ q) (hpq : q < p) (z : ℂ) (hz : z ≠ 0)
    (hderiv : cdim_laurent_double_frequency_critical_value_circle_derivative p q z = 0) :
    cdim_laurent_double_frequency_critical_value_circle_map p q z =
      ((p - q : ℂ) / (2 * p : ℂ)) * z ^ q := by
  have hp0_nat : p ≠ 0 := by omega
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp0_nat
  have hp_eq : p = q + (p - q) := by omega
  have hcrit :=
    (cdim_laurent_double_frequency_critical_value_circle_critical_equation p q hq hpq z hz).1 hderiv
  have hfactor : z ^ p + z ^ q = z ^ q * (z ^ (p - q) + 1) := by
    rw [hp_eq, pow_add, show q + (p - q) - q = p - q by omega]
    ring
  calc
    cdim_laurent_double_frequency_critical_value_circle_map p q z
        = (1 / 2 : ℂ) * (z ^ p + z ^ q) := by rfl
    _ = (1 / 2 : ℂ) * (z ^ q * (z ^ (p - q) + 1)) := by rw [hfactor]
    _ = (1 / 2 : ℂ) * (z ^ q * (-((q : ℂ) / (p : ℂ)) + 1)) := by rw [hcrit]
    _ = ((p - q : ℂ) / (2 * p : ℂ)) * z ^ q := by
          field_simp [hp0]
          ring

/-- Paper label: `thm:cdim-laurent-double-frequency-critical-value-circle`. -/
theorem paper_cdim_laurent_double_frequency_critical_value_circle
    (p q : ℕ) (hq : 1 ≤ q) (hpq : q < p) :
    cdim_laurent_double_frequency_critical_value_circle_statement p q := by
  refine ⟨?_, ?_, rfl⟩
  · exact fun z => fun hz =>
      cdim_laurent_double_frequency_critical_value_circle_critical_equation p q hq hpq z hz
  · exact fun z => fun hz => fun hderiv =>
      cdim_laurent_double_frequency_critical_value_circle_value_formula p q hq hpq z hz hderiv

end

end Omega.CircleDimension
