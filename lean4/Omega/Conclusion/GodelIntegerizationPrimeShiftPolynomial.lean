import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.PrimeRegister
import Omega.Conclusion.ShiftCommutingAlgorithmsPolynomial

namespace Omega.Conclusion

open Polynomial

/-- Polynomial coefficients in ascending order. -/
noncomputable def coefficientPolynomial : List ℕ → Polynomial ℤ
  | [] => 0
  | a :: coeffs => Polynomial.C (a : ℤ) + Polynomial.X * coefficientPolynomial coeffs

/-- Pointwise sum of exponent lists, padding the shorter list with zeros. -/
def addPad : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addPad xs ys

/-- Scalar multiplication on exponent lists. -/
def scaleList (a : ℕ) : List ℕ → List ℕ :=
  List.map (fun n => a * n)

/-- Shift-commuting polynomial action on finite exponent lists. -/
def phiPolynomial : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: coeffs, code => addPad (scaleList a code) (0 :: phiPolynomial coeffs code)

/-- The integerized prime-shift product attached to a polynomial coefficient list. -/
def primeShiftPolynomialValue (primes : ℕ → ℕ) (offset : ℕ) :
    List ℕ → List ℕ → ℕ
  | [], _ => 1
  | a :: coeffs, code =>
      godelEncoding primes offset code ^ a *
        primeShiftPolynomialValue primes (offset + 1) coeffs code

/-- Gödel integerization of the shift-commuting polynomial action. -/
def godelIntegerization (primes : ℕ → ℕ) (coeffs code : List ℕ) : ℕ :=
  godelEncoding primes 0 (phiPolynomial coeffs code)

theorem godelEncoding_addPad (primes : ℕ → ℕ) (offset : ℕ) (u v : List ℕ) :
    godelEncoding primes offset (addPad u v) =
      godelEncoding primes offset u * godelEncoding primes offset v := by
  induction u generalizing offset v with
  | nil =>
      simp [addPad, godelEncoding_nil]
  | cons a us ih =>
      cases v with
      | nil =>
          simp [addPad, godelEncoding_nil]
      | cons b vs =>
          simp [addPad, godelEncoding_cons, ih, pow_add, Nat.mul_assoc, Nat.mul_left_comm]

theorem godelEncoding_scaleList (primes : ℕ → ℕ) (offset a : ℕ) (code : List ℕ) :
    godelEncoding primes offset (scaleList a code) = godelEncoding primes offset code ^ a := by
  induction code generalizing offset with
  | nil =>
      simp [scaleList, godelEncoding_nil]
  | cons x xs ih =>
      rw [show scaleList a (x :: xs) = a * x :: scaleList a xs by simp [scaleList]]
      rw [godelEncoding_cons, godelEncoding_cons, ih]
      calc
        primes offset ^ (a * x) * godelEncoding primes (offset + 1) xs ^ a
            = (primes offset ^ x) ^ a * godelEncoding primes (offset + 1) xs ^ a := by
                rw [Nat.mul_comm a x, pow_mul]
        _ = (primes offset ^ x * godelEncoding primes (offset + 1) xs) ^ a := by rw [Nat.mul_pow]

theorem godelEncoding_shift_zero (primes : ℕ → ℕ) (offset : ℕ) (code : List ℕ) :
    godelEncoding primes offset (0 :: code) = godelEncoding primes (offset + 1) code := by
  rw [godelEncoding_cons]
  simp

theorem phiPolynomial_factorization (primes : ℕ → ℕ) (offset : ℕ)
    (coeffs code : List ℕ) :
    godelEncoding primes offset (phiPolynomial coeffs code) =
      primeShiftPolynomialValue primes offset coeffs code := by
  induction coeffs generalizing offset with
  | nil =>
      simp [phiPolynomial, primeShiftPolynomialValue, godelEncoding_nil]
  | cons a coeffs ih =>
      simp [phiPolynomial, primeShiftPolynomialValue, godelEncoding_addPad, godelEncoding_scaleList,
        godelEncoding_shift_zero, ih]

theorem primeShiftPolynomialValue_addPad (primes : ℕ → ℕ) (offset : ℕ)
    (f g code : List ℕ) :
    primeShiftPolynomialValue primes offset (addPad f g) code =
      primeShiftPolynomialValue primes offset f code *
        primeShiftPolynomialValue primes offset g code := by
  induction f generalizing offset g with
  | nil =>
      simp [addPad, primeShiftPolynomialValue]
  | cons a f ih =>
      cases g with
      | nil =>
          simp [addPad, primeShiftPolynomialValue]
      | cons b g =>
          simp [addPad, primeShiftPolynomialValue, ih, pow_add, Nat.mul_assoc, Nat.mul_left_comm]

/-- Paper-facing Gödel integerization formula: the shift-commuting action on exponent lists turns
into a product of prime shifts on the Gödel side, and the existing polynomial wrapper records the
unique polynomial code together with its additive and compositional identities. -/
theorem paper_conclusion_godel_integerization_prime_shift_polynomial
    (primes : ℕ → ℕ) (f g code : List ℕ) :
    let D : ShiftCommutingPolynomialData := ⟨coefficientPolynomial f⟩
    godelIntegerization primes f code = primeShiftPolynomialValue primes 0 f code ∧
      godelIntegerization primes (addPad f g) code =
        godelIntegerization primes f code * godelIntegerization primes g code ∧
      D.existsUniquePolynomialCode ∧ D.additionCompatibility ∧ D.compositionCompatibility := by
  intro D
  have hPoly := paper_conclusion_shift_commuting_algorithms_polynomial D
  refine ⟨?_, ?_, hPoly.1, hPoly.2.1, hPoly.2.2⟩
  · simpa [godelIntegerization] using phiPolynomial_factorization primes 0 f code
  · calc
      godelIntegerization primes (addPad f g) code
          = primeShiftPolynomialValue primes 0 (addPad f g) code := by
              simpa [godelIntegerization] using
                phiPolynomial_factorization primes 0 (addPad f g) code
      _ = primeShiftPolynomialValue primes 0 f code *
            primeShiftPolynomialValue primes 0 g code := by
              exact primeShiftPolynomialValue_addPad primes 0 f g code
      _ = godelIntegerization primes f code * godelIntegerization primes g code := by
            simpa [godelIntegerization] using
              congrArg₂ (· * ·)
                (phiPolynomial_factorization primes 0 f code).symm
                (phiPolynomial_factorization primes 0 g code).symm

end Omega.Conclusion
