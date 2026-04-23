import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The golden-resolution chain parameter `ρ_m`. -/
def xi_integrated_defect_golden_asymptotics_rho (m : ℕ) : ℝ :=
  Real.tanh ((1 / 2 : ℝ) * (m : ℝ) * Real.log Real.goldenRatio)

/-- The small parameter `ε_m = 1 - ρ_m^2`. -/
def xi_integrated_defect_golden_asymptotics_epsilon (m : ℕ) : ℝ :=
  1 - xi_integrated_defect_golden_asymptotics_rho m ^ 2

/-- Leading truncation of the integrated-defect asymptotic expansion. -/
def xi_integrated_defect_golden_asymptotics_leading (δ : ℝ) (m : ℕ) : ℝ :=
  2 * Real.pi * δ -
    4 * Real.sqrt δ * Real.sqrt (xi_integrated_defect_golden_asymptotics_epsilon m)

lemma xi_integrated_defect_golden_asymptotics_rho_closed_form (m : ℕ) :
    xi_integrated_defect_golden_asymptotics_rho m =
      (Real.goldenRatio ^ m - 1) / (Real.goldenRatio ^ m + 1) := by
  let t : ℝ := Real.goldenRatio ^ m
  let a : ℝ := Real.sqrt t
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 ht
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_t :
      Real.log t = (m : ℝ) * Real.log Real.goldenRatio := by
    dsimp [t]
    calc
      Real.log (Real.goldenRatio ^ m) = Real.log (Real.goldenRatio ^ (m : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (m : ℝ) * Real.log Real.goldenRatio := Real.log_rpow Real.goldenRatio_pos _
  have hlog_a :
      Real.log a = (1 / 2 : ℝ) * (m : ℝ) * Real.log Real.goldenRatio := by
    dsimp [a]
    rw [Real.log_sqrt (le_of_lt ht), hlog_t]
    ring
  have hsq : a ^ 2 = t := by
    dsimp [a]
    simpa [pow_two] using Real.sq_sqrt (le_of_lt ht)
  have hden_ne : a + a⁻¹ ≠ 0 := by
    have : 0 < a + a⁻¹ := by positivity
    linarith
  calc
    xi_integrated_defect_golden_asymptotics_rho m
        = Real.tanh (Real.log a) := by
            rw [xi_integrated_defect_golden_asymptotics_rho, hlog_a]
    _ = ((a - a⁻¹) / 2) / ((a + a⁻¹) / 2) := by
          rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_log ha_pos, Real.cosh_log ha_pos]
    _ = (t - 1) / (t + 1) := by
          field_simp [ha_ne, hden_ne]
          nlinarith [hsq]
    _ = (Real.goldenRatio ^ m - 1) / (Real.goldenRatio ^ m + 1) := by
          rfl

lemma xi_integrated_defect_golden_asymptotics_epsilon_closed_form (m : ℕ) :
    xi_integrated_defect_golden_asymptotics_epsilon m =
      4 * Real.goldenRatio ^ m / (Real.goldenRatio ^ m + 1) ^ 2 := by
  have hden_ne : (Real.goldenRatio ^ m + 1 : ℝ) ≠ 0 := by positivity
  rw [xi_integrated_defect_golden_asymptotics_epsilon,
    xi_integrated_defect_golden_asymptotics_rho_closed_form]
  field_simp [hden_ne]
  ring

lemma xi_integrated_defect_golden_asymptotics_leading_closed_form (δ : ℝ) (m : ℕ) :
    xi_integrated_defect_golden_asymptotics_leading δ m =
      2 * Real.pi * δ -
        8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
  have ht_pos : 0 < (Real.goldenRatio ^ m : ℝ) := by positivity
  have hden_pos : 0 < (Real.goldenRatio ^ m + 1 : ℝ) := by positivity
  have hsqrt :
      Real.sqrt (4 * Real.goldenRatio ^ m / (Real.goldenRatio ^ m + 1) ^ 2) =
        2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
    have hsq :
        (2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1)) ^ 2 =
          4 * Real.goldenRatio ^ m / (Real.goldenRatio ^ m + 1) ^ 2 := by
      field_simp [hden_pos.ne']
      rw [Real.sq_sqrt ht_pos.le]
      ring
    have hnonneg : 0 ≤ 2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
      positivity
    calc
      Real.sqrt (4 * Real.goldenRatio ^ m / (Real.goldenRatio ^ m + 1) ^ 2)
          = Real.sqrt
              ((2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1)) ^ 2) := by
                rw [hsq]
      _ = |2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1)| := by
            rw [Real.sqrt_sq_eq_abs]
      _ = 2 * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
            exact abs_of_nonneg hnonneg
  rw [xi_integrated_defect_golden_asymptotics_leading,
    xi_integrated_defect_golden_asymptotics_epsilon_closed_form, hsqrt]
  ring

/-- Paper label: `prop:xi-integrated-defect-golden-asymptotics`.
On the golden-resolution chain, the hyperbolic parameter has the exact closed form
`ρ_m = (φ^m - 1) / (φ^m + 1)`, hence `ε_m = 1 - ρ_m^2 = 4 φ^m / (φ^m + 1)^2`. The leading
integrated-defect truncation therefore has the explicit closed form
`2πδ - 8 √δ √(φ^m) / (φ^m + 1)`, and its deviation from the endpoint flux is
`O(φ^{-m/2})` in the concrete inequality recorded below. -/
theorem paper_xi_integrated_defect_golden_asymptotics (δ : ℝ) (hδ : 0 < δ) (m : ℕ) :
    xi_integrated_defect_golden_asymptotics_rho m =
      (Real.goldenRatio ^ m - 1) / (Real.goldenRatio ^ m + 1) ∧
    xi_integrated_defect_golden_asymptotics_epsilon m =
      4 * Real.goldenRatio ^ m / (Real.goldenRatio ^ m + 1) ^ 2 ∧
    xi_integrated_defect_golden_asymptotics_leading δ m =
      2 * Real.pi * δ -
        8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) ∧
    |xi_integrated_defect_golden_asymptotics_leading δ m - 2 * Real.pi * δ| ≤
      8 * Real.sqrt δ / Real.sqrt (Real.goldenRatio ^ m) := by
  have ht_pos : 0 < (Real.goldenRatio ^ m : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (Real.goldenRatio ^ m) := Real.sqrt_pos.2 ht_pos
  have hfrac_le :
      Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) ≤
        1 / Real.sqrt (Real.goldenRatio ^ m) := by
    have hsqrt_ne : Real.sqrt (Real.goldenRatio ^ m) ≠ 0 := ne_of_gt hsqrt_pos
    have hden_ne : (Real.goldenRatio ^ m + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hsqrt_ne, hden_ne]
    rw [Real.sq_sqrt ht_pos.le]
    linarith
  refine ⟨xi_integrated_defect_golden_asymptotics_rho_closed_form m,
    xi_integrated_defect_golden_asymptotics_epsilon_closed_form m,
    xi_integrated_defect_golden_asymptotics_leading_closed_form δ m, ?_⟩
  have hmain :
      |xi_integrated_defect_golden_asymptotics_leading δ m - 2 * Real.pi * δ| =
        8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
    have hnonneg :
        0 ≤ 8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
      positivity
    calc
      |xi_integrated_defect_golden_asymptotics_leading δ m - 2 * Real.pi * δ|
          = |-(8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) /
              (Real.goldenRatio ^ m + 1))| := by
                rw [xi_integrated_defect_golden_asymptotics_leading_closed_form]
                ring_nf
      _ = 8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1) := by
            rw [abs_neg, abs_of_nonneg hnonneg]
  rw [hmain]
  calc
    8 * Real.sqrt δ * Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1)
        = (8 * Real.sqrt δ) *
            (Real.sqrt (Real.goldenRatio ^ m) / (Real.goldenRatio ^ m + 1)) := by ring
    _ ≤ (8 * Real.sqrt δ) * (1 / Real.sqrt (Real.goldenRatio ^ m)) := by
          gcongr
    _ = 8 * Real.sqrt δ / Real.sqrt (Real.goldenRatio ^ m) := by ring

end

end Omega.Zeta
