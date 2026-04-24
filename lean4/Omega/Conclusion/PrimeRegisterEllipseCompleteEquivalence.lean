import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Prime-register exponent vectors, restricted to finite support on prime indices. -/
abbrev PrimeRegisterVector := {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p}

/-- Convert a positive integer into its prime-register exponent vector. -/
abbrev primeRegisterOfPNat : ℕ+ → PrimeRegisterVector :=
  Nat.factorizationEquiv

/-- Recover the positive integer encoded by a prime-register exponent vector. -/
abbrev primeRegisterNorm : PrimeRegisterVector → ℕ+ :=
  Nat.factorizationEquiv.symm

/-- Multiplication on prime registers transported from multiplication on positive integers via
unique prime factorization. -/
def primeRegisterMul (r s : PrimeRegisterVector) : PrimeRegisterVector :=
  primeRegisterOfPNat (primeRegisterNorm r * primeRegisterNorm s)

/-- The diagonal ellipse determined by a prime-register norm. The major axis is the norm, and the
minor axis is its reciprocal. -/
structure PrimeRegisterEllipse where
  majorAxis : ℕ+
  minorAxis : ℚ
  reciprocal_minor : minorAxis = (((majorAxis : ℕ) : ℚ)⁻¹)

/-- The diagonal action of the prime register on the unit circle, recorded by its axis lengths. -/
def primeRegisterEllipseMap (r : PrimeRegisterVector) : PrimeRegisterEllipse :=
  ⟨primeRegisterNorm r, (((primeRegisterNorm r : ℕ) : ℚ)⁻¹), rfl⟩

/-- The ellipse with major axis `n` and reciprocal minor axis. -/
def primeAxisEllipse (n : ℕ+) : PrimeRegisterEllipse :=
  ⟨n, (((n : ℕ) : ℚ)⁻¹), rfl⟩

/-- The transported multiplication law becomes multiplicativity of the norm. -/
def primeRegisterMonoidHomLaw : Prop :=
  ∀ r s : PrimeRegisterVector,
    primeRegisterNorm (primeRegisterMul r s) = primeRegisterNorm r * primeRegisterNorm s

/-- Recovering the major axis recovers the prime register itself. -/
def primeRegisterEllipseMapInjective : Prop :=
  Function.Injective primeRegisterEllipseMap

/-- The prime-register ellipses are exactly the diagonal ellipses with positive integer major
axis. -/
def primeRegisterEllipseImageClassification : Prop :=
  Set.range primeRegisterEllipseMap = Set.range primeAxisEllipse

/-- Paper-facing prime-register/ellipse equivalence package.
    prop:conclusion-prime-register-ellipse-complete-equivalence -/
theorem paper_conclusion_prime_register_ellipse_complete_equivalence :
    primeRegisterMonoidHomLaw ∧
      primeRegisterEllipseMapInjective ∧
      primeRegisterEllipseImageClassification := by
  refine ⟨?_, ?_, ?_⟩
  · intro r s
    simp [primeRegisterMul, primeRegisterNorm, primeRegisterOfPNat]
  · intro r s h
    have hAxis : primeRegisterNorm r = primeRegisterNorm s := by
      exact congrArg PrimeRegisterEllipse.majorAxis h
    exact Nat.factorizationEquiv.symm.injective hAxis
  · ext E
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨primeRegisterNorm r, rfl⟩
    · rintro ⟨n, rfl⟩
      refine ⟨primeRegisterOfPNat n, ?_⟩
      simp [primeRegisterEllipseMap, primeAxisEllipse, primeRegisterNorm, primeRegisterOfPNat]

end Omega.Conclusion
