import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

namespace Omega.EA

/-- Finitely supported digit configurations. Each index records the exponent of a prime register. -/
abbrev RegisterDigitCfg := ℕ →₀ ℕ

/-- Concrete prime-power products, written multiplicatively while storing the prime exponents. -/
abbrev PrimePowerProduct := Multiplicative RegisterDigitCfg

/-- The register-state map sends a digit configuration to the corresponding prime-power product. -/
def registerStateMap (a : RegisterDigitCfg) : PrimePowerProduct :=
  Multiplicative.ofAdd a

/-- Recover the prime exponents from a concrete prime-power product. -/
def primeExponents (x : PrimePowerProduct) : RegisterDigitCfg :=
  Multiplicative.toAdd x

@[simp] theorem primeExponents_registerStateMap (a : RegisterDigitCfg) :
    primeExponents (registerStateMap a) = a := rfl

@[simp] theorem registerStateMap_primeExponents (x : PrimePowerProduct) :
    registerStateMap (primeExponents x) = x := by
  cases x
  rfl

theorem registerStateMap_hom (a b : RegisterDigitCfg) :
    registerStateMap (a + b) = registerStateMap a * registerStateMap b := rfl

theorem registerStateMap_injective : Function.Injective registerStateMap := by
  intro a b hab
  exact congrArg primeExponents hab

theorem registerStateMap_surjective : Function.Surjective registerStateMap := by
  intro x
  exact ⟨primeExponents x, registerStateMap_primeExponents x⟩

/-- The prime-register monoid is concretely realized by finitely supported exponent vectors:
addition of register states becomes multiplication of prime-power products, and unique exponent
vectors give both injectivity and surjectivity of the realization map.
    prop:prime-register-monoid-realization -/
theorem paper_prime_register_monoid_realization :
    (∀ a b : RegisterDigitCfg, registerStateMap (a + b) = registerStateMap a * registerStateMap b)
      ∧
    Function.Injective registerStateMap ∧
    Function.Surjective registerStateMap := by
  exact ⟨registerStateMap_hom, registerStateMap_injective, registerStateMap_surjective⟩

end Omega.EA
