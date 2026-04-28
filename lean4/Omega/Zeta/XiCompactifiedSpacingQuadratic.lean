import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The height-axis zero-spacing law at a fixed height. -/
def xi_compactified_spacing_quadratic_zero_spacing_law
    (pi logT deltaT : ℝ) : Prop :=
  deltaT = 2 * pi / logT

/-- The compactification derivative law at a fixed height. -/
def xi_compactified_spacing_quadratic_compactification_derivative_law
    (T pi deriv : ℝ) : Prop :=
  deriv = 1 / (pi * T ^ 2)

/-- The resulting quadratic compactified spacing law. -/
def xi_compactified_spacing_quadratic_compactified_spacing_law
    (T logT deltaU : ℝ) : Prop :=
  deltaU = 2 / (T ^ 2 * logT)

/-- Dyadic depth is the negative base-two logarithm of the compactified spacing. -/
def xi_compactified_spacing_quadratic_dyadic_depth_law
    (deltaU depth : ℝ) : Prop :=
  depth = - Real.log deltaU / Real.log 2

/-- Paper label: `cor:xi-compactified-spacing-quadratic`. -/
theorem paper_xi_compactified_spacing_quadratic
    {T pi logT deltaT deriv deltaU depth : ℝ}
    (hpi : pi ≠ 0) (hT : T ≠ 0) (hlogT : logT ≠ 0)
    (hZero : xi_compactified_spacing_quadratic_zero_spacing_law pi logT deltaT)
    (hDeriv : xi_compactified_spacing_quadratic_compactification_derivative_law T pi deriv)
    (hTransport : deltaU = deltaT * deriv)
    (hDepth : xi_compactified_spacing_quadratic_dyadic_depth_law deltaU depth) :
    xi_compactified_spacing_quadratic_compactified_spacing_law T logT deltaU ∧
      xi_compactified_spacing_quadratic_dyadic_depth_law deltaU depth := by
  refine ⟨?_, hDepth⟩
  change deltaU = 2 / (T ^ 2 * logT)
  rw [hTransport]
  rw [xi_compactified_spacing_quadratic_zero_spacing_law] at hZero
  rw [xi_compactified_spacing_quadratic_compactification_derivative_law] at hDeriv
  rw [hZero, hDeriv]
  field_simp [hpi, hT, hlogT]

end Omega.Zeta
