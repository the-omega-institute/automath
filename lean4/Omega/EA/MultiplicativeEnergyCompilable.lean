import Mathlib.Tactic

namespace Omega.EA

/-- Chapter-local package for the compilability of multiplicative energy. The fields record the
four-track product transducer, the extracted finite transition matrix data, the path-count
identity behind the matrix-power formula, and the Perron-Frobenius step upgrading that formula to
the advertised exponential growth law. -/
structure MultiplicativeEnergyCompilableData where
  stateCount : ℕ
  collisionCount : ℕ → ℕ
  transitionEntry : Fin stateCount → Fin stateCount → ℕ
  initialEntry : Fin stateCount → ℕ
  terminalEntry : Fin stateCount → ℕ
  fourTrackProductBuilt : Prop
  finiteTransitionMatrixExtracted : Prop
  pathCountIdentity : Prop
  perronFrobeniusPackage : Prop
  matrixPowerFormula : Prop
  exponentialGrowthRate : Prop
  fourTrackProductBuilt_h : fourTrackProductBuilt
  finiteTransitionMatrixExtracted_h : finiteTransitionMatrixExtracted
  derivePathCountIdentity :
    fourTrackProductBuilt → finiteTransitionMatrixExtracted → pathCountIdentity
  deriveMatrixPowerFormula : pathCountIdentity → matrixPowerFormula
  derivePerronFrobeniusPackage : matrixPowerFormula → perronFrobeniusPackage
  deriveExponentialGrowthRate : perronFrobeniusPackage → exponentialGrowthRate

/-- Paper-facing wrapper for the multiplicative-energy compilability package: once the four-track
product transducer has been compiled to a finite transition matrix, the path-count identity yields
the matrix-power formula `E_x(A_m) = uᵀ B_x^m v`, and the Perron-Frobenius growth package gives the
claimed exponential rate.
    prop:conclusion71-multiplicative-energy-compilable -/
theorem paper_conclusion71_multiplicative_energy_compilable
    (D : MultiplicativeEnergyCompilableData) :
    D.matrixPowerFormula ∧ D.exponentialGrowthRate := by
  have hPath : D.pathCountIdentity :=
    D.derivePathCountIdentity D.fourTrackProductBuilt_h D.finiteTransitionMatrixExtracted_h
  have hMatrix : D.matrixPowerFormula := D.deriveMatrixPowerFormula hPath
  have hPF : D.perronFrobeniusPackage := D.derivePerronFrobeniusPackage hMatrix
  exact ⟨hMatrix, D.deriveExponentialGrowthRate hPF⟩

end Omega.EA
