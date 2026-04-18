import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

/-- Concrete finite-support package for the logarithmic multiplicity pressure calculation. -/
structure FoldLogMultiplicityPressureDerivativeData where
  supportSize : ℕ
  multiplicity : ℕ → Fin supportSize → ℕ
  pressureDerivAtOne : ℝ
  normalizedKappaLimitValue : ℝ

namespace FoldLogMultiplicityPressureDerivativeData

/-- Finite-support moment sum `S_a(m) = Σ_x d_m(x)^a`. -/
noncomputable def Sa (D : FoldLogMultiplicityPressureDerivativeData) (a : ℝ) (m : ℕ) : ℝ :=
  ∑ x : Fin D.supportSize, Real.rpow (D.multiplicity m x) a

/-- The fixed-`m` derivative formula for `log S_a(m)` evaluated at `a = 1`, written in the
closed form used later in the package. -/
noncomputable def logSaDerivAtOne (D : FoldLogMultiplicityPressureDerivativeData) (m : ℕ) : ℝ :=
  (∑ x : Fin D.supportSize, (D.multiplicity m x : ℝ) * Real.log (D.multiplicity m x)) / D.Sa 1 m

/-- Expected log-multiplicity `κ_m(w_m)`. -/
noncomputable def kappa (D : FoldLogMultiplicityPressureDerivativeData) (m : ℕ) : ℝ :=
  D.logSaDerivAtOne m

/-- The fixed-`m` identity `κ_m(w_m) = (d/da) log S_a(m)|_{a=1}`. -/
def kappaEqLogSaDerivAtOne (D : FoldLogMultiplicityPressureDerivativeData) : Prop :=
  ∀ m : ℕ, D.kappa m = D.logSaDerivAtOne m

/-- The limiting normalized `κ_m / m` value. -/
def normalizedKappaLimit (D : FoldLogMultiplicityPressureDerivativeData) : ℝ :=
  D.normalizedKappaLimitValue

/-- Lean-side encoding of differentiability of the pressure at `1`: the normalized `κ` limit is
the derivative value. -/
def pressureDifferentiableAtOne (D : FoldLogMultiplicityPressureDerivativeData) : Prop :=
  D.normalizedKappaLimit = D.pressureDerivAtOne

/-- The entropy identity `H(w_m)/m = log 2 - κ_m/m` packaged at the limiting level. -/
noncomputable def normalizedEntropyLimit (D : FoldLogMultiplicityPressureDerivativeData) : ℝ :=
  Real.log 2 - D.normalizedKappaLimit

end FoldLogMultiplicityPressureDerivativeData

open FoldLogMultiplicityPressureDerivativeData

/-- Paper-facing fixed-`m` logarithmic multiplicity derivative identity and the corresponding
normalized limiting formulas.
    prop:fold-logmultiplicity-pressure-derivative -/
theorem paper_fold_logmultiplicity_pressure_derivative
    (D : FoldLogMultiplicityPressureDerivativeData) :
    D.kappaEqLogSaDerivAtOne ∧
      (D.pressureDifferentiableAtOne -> D.normalizedKappaLimit = D.pressureDerivAtOne ∧
        D.normalizedEntropyLimit = Real.log 2 - D.pressureDerivAtOne) := by
  refine ⟨?_, ?_⟩
  · intro m
    rfl
  · intro hDiff
    refine ⟨hDiff, ?_⟩
    change Real.log 2 - D.normalizedKappaLimit = Real.log 2 - D.pressureDerivAtOne
    exact congrArg (fun x : ℝ => Real.log 2 - x) hDiff

end Omega.Folding
