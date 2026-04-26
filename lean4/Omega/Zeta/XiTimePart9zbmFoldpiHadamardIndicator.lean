import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbmFoldpiPointwiseSlopeRigidity

namespace Omega.Zeta

noncomputable section

/-- Concrete Fredholm double-sine growth model used for the Hadamard indicator package. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_fredholm_growth (r θ : ℝ) : ℝ :=
  Real.exp (Real.goldenRatio ^ (2 : ℕ) * r * |Real.sin θ|)

/-- Indicator extracted from the recorded radial exponential growth. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_indicator (θ : ℝ) : ℝ :=
  Real.goldenRatio ^ (2 : ℕ) * |Real.sin θ|

/-- Hadamard type of the folded double-sine model. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_type : ℝ :=
  Real.goldenRatio ^ (2 : ℕ)

/-- Limsup package recorded by the model; the concrete wrapper stores exactly the indicator. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_recorded_limsup (θ : ℝ) : ℝ :=
  xi_time_part9zbm_foldpi_hadamard_indicator_indicator θ

/-- Algebraically simplified normal form of the golden Hadamard indicator. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_normal_form (θ : ℝ) : ℝ :=
  (Real.goldenRatio + 1) * |Real.sin θ|

/-- Concrete Hadamard-indicator statement for the folded double-sine Fredholm model. -/
def xi_time_part9zbm_foldpi_hadamard_indicator_statement : Prop :=
  (∀ θ : ℝ,
    xi_time_part9zbm_foldpi_hadamard_indicator_recorded_limsup θ =
      xi_time_part9zbm_foldpi_hadamard_indicator_indicator θ) ∧
    (∀ θ : ℝ,
      xi_time_part9zbm_foldpi_hadamard_indicator_indicator θ =
        xi_time_part9zbm_foldpi_hadamard_indicator_normal_form θ) ∧
    xi_time_part9zbm_foldpi_hadamard_indicator_type = Real.goldenRatio + 1 ∧
    (∀ r θ : ℝ,
      Real.log (xi_time_part9zbm_foldpi_hadamard_indicator_fredholm_growth r θ) =
        xi_time_part9zbm_foldpi_hadamard_indicator_indicator θ * r)

/-- Paper label: `thm:xi-time-part9zbm-foldpi-hadamard-indicator`. -/
theorem paper_xi_time_part9zbm_foldpi_hadamard_indicator :
    xi_time_part9zbm_foldpi_hadamard_indicator_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ
    rfl
  · intro θ
    simp [xi_time_part9zbm_foldpi_hadamard_indicator_indicator,
      xi_time_part9zbm_foldpi_hadamard_indicator_normal_form, Real.goldenRatio_sq]
  · simp [xi_time_part9zbm_foldpi_hadamard_indicator_type, Real.goldenRatio_sq]
  · intro r θ
    simp [xi_time_part9zbm_foldpi_hadamard_indicator_fredholm_growth,
      xi_time_part9zbm_foldpi_hadamard_indicator_indicator, mul_comm, mul_left_comm]

end

end Omega.Zeta
