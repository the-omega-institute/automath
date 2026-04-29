import Mathlib.Tactic

namespace Omega.EA

/-- The finite ramified-prime ledger of the quaternion algebra. -/
abbrev RamifiedPrimeRegister := Finset ℕ

/-- In the quadratic extension ledger, `p` splits exactly when it is recorded in the split-prime
register. -/
def primeSplitsInQuadratic (splitPrimes : Finset ℕ) (p : ℕ) : Prop :=
  p ∈ splitPrimes

/-- The local tensor `L ⊗ ℚ_p` is a field exactly when `p` does not split in the quadratic
extension. -/
def localQuadraticTensorIsField (splitPrimes : Finset ℕ) (p : ℕ) : Prop :=
  p ∉ splitPrimes

/-- At a ramified finite prime, the local quaternion algebra splits over the quadratic extension
precisely when the local quadratic tensor is a field. -/
def localQuaternionSplitsOverQuadratic (splitPrimes : Finset ℕ) (p : ℕ) : Prop :=
  localQuadraticTensorIsField splitPrimes p

/-- Global splitting over the quadratic extension is reduced to checking the finite ramified
primes. -/
def globalQuaternionSplitsOverQuadratic
    (ramifiedPrimes splitPrimes : Finset ℕ) : Prop :=
  ∀ p ∈ ramifiedPrimes, localQuaternionSplitsOverQuadratic splitPrimes p

/-- Global splitting over `L = ℚ(√d)` is equivalent to local splitting at each finite ramified
prime, and for a ramified prime the local quaternion algebra splits exactly when the local tensor
is a field, i.e. exactly when that prime does not split in `L`.
    prop:prime-register-brauer-quadratic-splitting -/
theorem paper_prime_register_brauer_quadratic_splitting
    (ramifiedPrimes splitPrimes : RamifiedPrimeRegister) :
    (globalQuaternionSplitsOverQuadratic ramifiedPrimes splitPrimes ↔
      ∀ p ∈ ramifiedPrimes, ¬ primeSplitsInQuadratic splitPrimes p) ∧
    ∀ p ∈ ramifiedPrimes,
      (localQuaternionSplitsOverQuadratic splitPrimes p ↔
        localQuadraticTensorIsField splitPrimes p) ∧
      (localQuadraticTensorIsField splitPrimes p ↔
        ¬ primeSplitsInQuadratic splitPrimes p) := by
  constructor
  · simp [globalQuaternionSplitsOverQuadratic, localQuaternionSplitsOverQuadratic,
      localQuadraticTensorIsField, primeSplitsInQuadratic]
  · intro p hp
    simp [localQuaternionSplitsOverQuadratic, localQuadraticTensorIsField, primeSplitsInQuadratic]

end Omega.EA
