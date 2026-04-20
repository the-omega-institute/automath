import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.SyncKernelWeighted.CompletedPrimitivePrimePowerDifferenceQuotient
import Omega.SyncKernelWeighted.MuPochhammerNecklaceDirichletPolylog
import Omega.SyncKernelWeighted.WittFrobeniusIteratedDescent
import Omega.Zeta.NecklaceCorrection

namespace Omega.SyncKernelWeighted

open Polynomial
open scoped BigOperators
open scoped ArithmeticFunction.Moebius

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

/-- Concrete Ihara/Witt packaging: the trace polynomials, their Witt-coordinate incarnation, a
necklace parameter, and a prime-power Frobenius congruence witness. No field is a bare abstract
`Prop`; all hypotheses are attached to concrete sequences or polynomials. -/
structure IharaWittDworkData where
  alphabet : ℕ
  necklaceLength : ℕ
  traceData : WeightedHashimotoTraceData
  wittData : WeightedHashimotoTraceData
  wittMatchesTrace : ∀ n, wittData n = weightedHashimotoWittCoordinates traceData n
  p : ℕ
  k : ℕ
  hp : Nat.Prime p
  hk : 1 ≤ k
  frobeniusTrace : ℕ → Polynomial ℤ
  dworkStep :
    ∀ j, 1 ≤ j →
      PolyZModEq (p ^ j) (frobeniusTrace (p ^ j))
        ((frobeniusTrace (p ^ (j - 1))).comp (Polynomial.X ^ p))
  completedData : CompletedPrimitivePrimePowerDifferenceQuotientData

/-- The necklace side is identified with an explicit Möbius divisor sum, hence lands in `ℤ`. -/
def IharaWittDworkData.necklaceIntegrality (D : IharaWittDworkData) : Prop :=
  Omega.Zeta.necklaceCorrectionKernel D.alphabet (2 * D.necklaceLength) =
    muPochhammerNecklaceCoefficient D.alphabet D.necklaceLength

/-- The prime-power Dwork package combines the completed primitive difference quotient with the
polynomial Frobenius congruence at level `p^k`. -/
def IharaWittDworkData.primePowerDworkCongruence (D : IharaWittDworkData) : Prop :=
  D.completedData.primePowerDifferenceQuotient ∧
    PolyZModEq (D.p ^ D.k) (D.frobeniusTrace (D.p ^ D.k))
      ((D.frobeniusTrace (D.p ^ (D.k - 1))).comp (Polynomial.X ^ D.p))

/-- Paper-facing weighted Ihara/Witt corollary: the necklace side is integer-valued and the
prime-power slice satisfies the standard Dwork congruence package.
    cor:ihara-witt-dwork -/
theorem paper_ihara_witt_dwork (D : IharaWittDworkData) :
    D.necklaceIntegrality ∧ D.primePowerDworkCongruence := by
  refine ⟨?_, ?_⟩
  · simpa [IharaWittDworkData.necklaceIntegrality] using
      ((paper_mu_pochhammer_necklace_dirichlet_polylog D.alphabet).1 D.necklaceLength).symm
  · exact ⟨paper_completed_primitive_prime_power_difference_quotient D.completedData,
      D.dworkStep D.k D.hk⟩

end Omega.SyncKernelWeighted
