import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- Concrete one-state Markov data for the determinant/derivative bad-prime package. The Green
kernel and its denominator are recorded explicitly so that the denominator obstruction can be
stated without introducing any abstract shell assumptions. -/
structure XiMarkovDerivativeDeterminantBadPrimeData where
  greenKernel : Matrix (Fin 1) (Fin 1) ℚ
  greenDenominator : ℤ
  hgreenKernel : greenKernel = 1
  hgreenDenominator : greenDenominator = 1

namespace XiMarkovDerivativeDeterminantBadPrimeData

/-- The one-state transition matrix. -/
def transition : Matrix (Fin 1) (Fin 1) ℤ :=
  1

/-- The stationary rank-one projector `1 πᵀ` in the one-state model. -/
def stationaryProjector : Matrix (Fin 1) (Fin 1) ℤ :=
  1

/-- The corrected matrix `A = I - T + 1 πᵀ`. -/
def correction : Matrix (Fin 1) (Fin 1) ℤ :=
  1 - transition + stationaryProjector

/-- The derivative of the transition characteristic polynomial evaluated at `1`. -/
noncomputable def charpolyDerivativeAtOne : ℤ :=
  (transition.charpoly.derivative).eval 1

/-- Bad primes are exactly those for which the determinant of `A` vanishes modulo `p`. -/
def badPrime (_D : XiMarkovDerivativeDeterminantBadPrimeData) (p : ℕ) : Prop :=
  Nat.Prime p ∧ (((correction.det : ℤ) : ZMod p) = 0)

/-- A double root at `1` modulo `p` is detected by vanishing of the derivative there. -/
def doubleRootAtOne (_D : XiMarkovDerivativeDeterminantBadPrimeData) (p : ℕ) : Prop :=
  Nat.Prime p ∧ (((charpolyDerivativeAtOne : ℤ) : ZMod p) = 0)

/-- Determinant/characteristic-polynomial derivative identity for the corrected matrix. -/
def det_eq_charpoly_derivative (_D : XiMarkovDerivativeDeterminantBadPrimeData) : Prop :=
  correction.det = charpolyDerivativeAtOne

/-- A prime is bad exactly when the characteristic polynomial has a double root at `1` modulo
that prime. -/
def bad_prime_iff_double_root (D : XiMarkovDerivativeDeterminantBadPrimeData) : Prop :=
  ∀ p, Nat.Prime p → (D.badPrime p ↔ D.doubleRootAtOne p)

/-- If the Green kernel denominator vanishes modulo `p`, then `p` must already be bad for the
corrected determinant. The first conjunct records that the chosen Green kernel is indeed `A⁻¹`. -/
def green_denominator_obstruction (D : XiMarkovDerivativeDeterminantBadPrimeData) : Prop :=
  D.greenKernel = ((correction.map (Int.castRingHom ℚ))⁻¹) ∧
    ∀ p, Nat.Prime p → ((((D.greenDenominator : ℤ) : ZMod p) = 0) → D.badPrime p)

lemma correction_eq_one :
    correction = (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [correction, transition, stationaryProjector]

lemma correction_det_eq_one :
    correction.det = 1 := by
  rw [correction_eq_one]
  simp

lemma charpolyDerivativeAtOne_eq_one :
    charpolyDerivativeAtOne = 1 := by
  unfold charpolyDerivativeAtOne transition
  have hchar : Matrix.charpoly (1 : Matrix (Fin 1) (Fin 1) ℤ) = X - 1 := by
    simpa using (Matrix.charpoly_one (n := Fin 1) (R := ℤ))
  rw [hchar]
  simp

lemma det_eq_charpoly_derivative_holds (D : XiMarkovDerivativeDeterminantBadPrimeData) :
    D.det_eq_charpoly_derivative := by
  rw [det_eq_charpoly_derivative, correction_det_eq_one, charpolyDerivativeAtOne_eq_one]

lemma bad_prime_iff_double_root_holds (D : XiMarkovDerivativeDeterminantBadPrimeData) :
    D.bad_prime_iff_double_root := by
  intro p hp
  constructor
  · intro hBad
    exact ⟨hp, by
      have hzero : (((correction.det : ℤ) : ZMod p) = 0) := hBad.2
      rwa [D.det_eq_charpoly_derivative_holds] at hzero⟩
  · intro hRoot
    exact ⟨hp, by
      have hzero : (((charpolyDerivativeAtOne : ℤ) : ZMod p) = 0) := hRoot.2
      rwa [← D.det_eq_charpoly_derivative_holds] at hzero⟩

lemma green_denominator_obstruction_holds (D : XiMarkovDerivativeDeterminantBadPrimeData) :
    D.green_denominator_obstruction := by
  refine ⟨?_, ?_⟩
  · calc
      D.greenKernel = 1 := D.hgreenKernel
      _ = ((correction.map (Int.castRingHom ℚ))⁻¹) := by
            rw [correction_eq_one]
            simp
  · intro p hp hzero
    letI : Fact p.Prime := ⟨hp⟩
    have hone : (((1 : ℤ) : ZMod p) ≠ 0) := by
      simp
    have : (((1 : ℤ) : ZMod p) = 0) := by
      simp [D.hgreenDenominator] at hzero
    exact False.elim (hone this)

end XiMarkovDerivativeDeterminantBadPrimeData

open XiMarkovDerivativeDeterminantBadPrimeData

/-- In the one-state Markov model, the corrected determinant equals the derivative of the
characteristic polynomial at `1`; therefore bad primes are exactly the primes for which `1` is a
double root modulo `p`, and any denominator obstruction for the Green kernel would have to come
from the same bad-prime set.
    thm:xi-markov-derivative-determinant-bad-prime -/
theorem paper_xi_markov_derivative_determinant_bad_prime
    (D : XiMarkovDerivativeDeterminantBadPrimeData) :
    D.det_eq_charpoly_derivative ∧ D.bad_prime_iff_double_root ∧ D.green_denominator_obstruction :=
  by
  exact ⟨D.det_eq_charpoly_derivative_holds, D.bad_prime_iff_double_root_holds,
    D.green_denominator_obstruction_holds⟩

end Omega.Zeta
