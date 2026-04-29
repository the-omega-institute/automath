import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter Topology

noncomputable section

/-- Concrete finite Hankel singular-value model with an exponential modulus. -/
structure xi_leyang_hankel_singular_slope_detects_moduli_data where
  modulus : ℝ
  singularValue : ℕ → ℝ
  singularValue_formula :
    ∀ n : ℕ, singularValue n = Real.exp (-(n : ℝ) * modulus)

/-- The logarithmic slope extracted from the positive Hankel singular-value sequence. -/
def xi_leyang_hankel_singular_slope_detects_moduli_logSlope
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) (n : ℕ) : ℝ :=
  -Real.log (D.singularValue (n + 1)) / ((n + 1 : ℕ) : ℝ)

/-- The lower exponential estimate in the exact finite model. -/
def xi_leyang_hankel_singular_slope_detects_moduli_lowerEstimate
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) * D.modulus)

/-- The upper exponential estimate in the exact finite model. -/
def xi_leyang_hankel_singular_slope_detects_moduli_upperEstimate
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) * D.modulus)

/-- Two-sided exponential Hankel singular-value estimates. -/
def xi_leyang_hankel_singular_slope_detects_moduli_twoSidedEstimates
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) : Prop :=
  ∀ n : ℕ,
    xi_leyang_hankel_singular_slope_detects_moduli_lowerEstimate D n ≤ D.singularValue n ∧
      D.singularValue n ≤ xi_leyang_hankel_singular_slope_detects_moduli_upperEstimate D n

/-- Concrete paper-facing limit package: positivity, two-sided exponential control, and recovery of
the modulus as the logarithmic singular-slope limit. -/
def xi_leyang_hankel_singular_slope_detects_moduli_statement
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) : Prop :=
  (∀ n : ℕ, 0 < D.singularValue n) ∧
    xi_leyang_hankel_singular_slope_detects_moduli_twoSidedEstimates D ∧
      Tendsto (xi_leyang_hankel_singular_slope_detects_moduli_logSlope D) atTop
        (𝓝 D.modulus)

/-- Paper label: `thm:xi-leyang-hankel-singular-slope-detects-moduli`. -/
theorem paper_xi_leyang_hankel_singular_slope_detects_moduli
    (D : xi_leyang_hankel_singular_slope_detects_moduli_data) :
    xi_leyang_hankel_singular_slope_detects_moduli_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [D.singularValue_formula n]
    positivity
  · intro n
    rw [D.singularValue_formula n]
    simp [xi_leyang_hankel_singular_slope_detects_moduli_lowerEstimate,
      xi_leyang_hankel_singular_slope_detects_moduli_upperEstimate]
  · have hSlope :
        xi_leyang_hankel_singular_slope_detects_moduli_logSlope D =
          fun _n : ℕ => D.modulus := by
      funext n
      have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      rw [xi_leyang_hankel_singular_slope_detects_moduli_logSlope,
        D.singularValue_formula (n + 1), Real.log_exp]
      field_simp [hn]
    rw [hSlope]
    exact tendsto_const_nhds

end

end Omega.Zeta
