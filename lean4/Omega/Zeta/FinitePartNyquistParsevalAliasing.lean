import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete spectral data for the Nyquist/Parseval identity. The continuous energy is the
spectral energy, and the discrete energy is the spectral term plus the aliasing correction. -/
structure NyquistParsevalData where
  spectralEnergy : Complex
  aliasingCorrection : Nat → Complex

/-- Continuous Parseval energy. -/
def NyquistParsevalData.continuousEnergy (D : NyquistParsevalData) : Complex :=
  D.spectralEnergy

/-- Discrete Nyquist sampling energy at depth `q`. -/
def NyquistParsevalData.discreteEnergy (D : NyquistParsevalData) (q : Nat) : Complex :=
  D.spectralEnergy + D.aliasingCorrection q

/-- Paper label: `thm:finite-part-nyquist-parseval-aliasing`. -/
theorem paper_finite_part_nyquist_parseval_aliasing
    (D : NyquistParsevalData) (q : Nat) :
    And (D.continuousEnergy = D.spectralEnergy)
      (D.discreteEnergy q = D.spectralEnergy + D.aliasingCorrection q) := by
  constructor <;> rfl

end Omega.Zeta
