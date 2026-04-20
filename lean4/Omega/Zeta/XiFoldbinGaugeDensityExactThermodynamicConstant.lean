import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.GroupoidCentralRenyiShannon
import Omega.Zeta.XiFoldbinGaugeEntropyOneNatLaw

namespace Omega.Zeta

/-- The explicit thermodynamic main term appearing in the foldbin gauge-density asymptotic. -/
noncomputable def xiFoldbinGaugeDensityThermodynamicMain (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log (2 / Real.goldenRatio) - 1 -
    Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)

/-- Concrete wrapper for the exact thermodynamic constant: the main term is exactly the gauge
one-nat law after substituting the Shannon term `m log φ + (log φ)/(1 + φ²)`, the constant offset
is the claimed `-1 - (log φ)/(1 + φ²)`, and the model error scale is nonnegative. -/
def XiFoldbinGaugeDensityExactThermodynamicConstantStatement (m : ℕ) : Prop :=
  xiFoldbinGaugeDensityThermodynamicMain m =
      (m : ℝ) * Real.log 2 -
        ((m : ℝ) * Real.log Real.goldenRatio +
          Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2)) - 1 ∧
    xiFoldbinGaugeDensityThermodynamicMain m - (m : ℝ) * Real.log (2 / Real.goldenRatio) =
      -1 - Real.log Real.goldenRatio / (1 + Real.goldenRatio ^ 2) ∧
    0 ≤ (m : ℝ) * (Real.goldenRatio / 2) ^ m

/-- Paper label: `thm:xi-foldbin-gauge-density-exact-thermodynamic-constant`. Substituting the
Shannon asymptotic into the one-nat gauge-density law collapses the linear term to
`m log (2 / φ)` and isolates the exact constant `-1 - (log φ)/(1 + φ²)`. -/
theorem paper_xi_foldbin_gauge_density_exact_thermodynamic_constant (m : ℕ) :
    XiFoldbinGaugeDensityExactThermodynamicConstantStatement m := by
  have hlog :
      Real.log (2 / Real.goldenRatio) = Real.log 2 - Real.log Real.goldenRatio := by
    rw [Real.log_div (show (2 : ℝ) ≠ 0 by norm_num) Real.goldenRatio_ne_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [xiFoldbinGaugeDensityThermodynamicMain, hlog]
    ring
  · simp [xiFoldbinGaugeDensityThermodynamicMain]
    ring
  · positivity

end Omega.Zeta
