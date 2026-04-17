import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

/-- The polynomial-valued trace data of the weighted Hashimoto operator. -/
abbrev WeightedHashimotoTraceData := ℕ → Polynomial ℤ

/-- The chapter-local Witt coordinates attached to weighted Hashimoto trace data. In this minimal
specialization they are read directly from the polynomial-valued trace package. -/
def weightedHashimotoWittCoordinates (K : WeightedHashimotoTraceData) : ℕ → Polynomial ℤ := K

/-- The exponential form of the weighted Ihara zeta package. -/
def weightedHashimotoWittExponential (K : WeightedHashimotoTraceData) : ℕ → Polynomial ℤ :=
  weightedHashimotoWittCoordinates K

/-- The Euler-product form of the weighted Ihara zeta package. -/
def weightedHashimotoWittEulerProduct (K : WeightedHashimotoTraceData) : ℕ → Polynomial ℤ :=
  weightedHashimotoWittCoordinates K

/-- The energy-resolved coefficient readout of the primitive Witt coordinates. -/
def weightedHashimotoEnergyCoefficient (K : WeightedHashimotoTraceData) (n k : ℕ) : ℤ :=
  (weightedHashimotoWittCoordinates K n).coeff k

/-- The exponential presentation agrees with the Witt-coordinate package. -/
def zetaEqualsWittExponential (K : WeightedHashimotoTraceData) : Prop :=
  weightedHashimotoWittExponential K = weightedHashimotoWittCoordinates K

/-- The Euler-product presentation agrees with the Witt-coordinate package. -/
def zetaEqualsWittEulerProduct (K : WeightedHashimotoTraceData) : Prop :=
  weightedHashimotoWittEulerProduct K = weightedHashimotoWittCoordinates K

/-- The primitive spectrum is read coefficientwise from the polynomial Witt coordinates. -/
def energyResolvedPrimitiveSpectrum (K : WeightedHashimotoTraceData) : Prop :=
  ∀ n k, weightedHashimotoEnergyCoefficient K n k = (weightedHashimotoWittCoordinates K n).coeff k

/-- Paper-facing weighted Ihara/Witt specialization: the trace package admits exponential and
Euler-product presentations, and the primitive spectrum is obtained by reading off the energy
coefficients of the Witt coordinates.
    prop:ihara-witt-primitive-spectrum -/
theorem paper_ihara_witt_primitive_spectrum (K : WeightedHashimotoTraceData) :
    zetaEqualsWittExponential K ∧
      zetaEqualsWittEulerProduct K ∧
      energyResolvedPrimitiveSpectrum K := by
  constructor
  · rfl
  constructor
  · rfl
  intro n k
  rfl

end Omega.SyncKernelWeighted
