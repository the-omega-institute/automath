import Mathlib.Tactic

namespace Omega.Folding

/-- Prime-register objects are encoded by their exponent functions on `Fin n`. -/
abbrev PrimeRegister (n : ℕ) := Fin n → Fin n

/-- The `qᵢ`-valuation is just the `i`-th coordinate of the exponent register. -/
def primeRegisterValuation {n : ℕ} (N : PrimeRegister n) (i : Fin n) : Fin n :=
  N i

/-- The register product induced by valuation composition. -/
def primeRegisterMul {n : ℕ} (M N : PrimeRegister n) : PrimeRegister n :=
  fun i => primeRegisterValuation M (primeRegisterValuation N i)

structure PrimeValuationArithmetizationData (n : ℕ) where
  primes : Fin n → ℕ := fun i => i.1 + 2

/-- The arithmetization map sends a register object to its valuation function. -/
def PrimeValuationArithmetizationData.phi {n : ℕ} (_ : PrimeValuationArithmetizationData n) :
    PrimeRegister n → (Fin n → Fin n) :=
  fun N => primeRegisterValuation N

/-- The inverse arithmetization rebuilds the register from its coordinate data. -/
def PrimeValuationArithmetizationData.phiInv {n : ℕ} (_ : PrimeValuationArithmetizationData n) :
    (Fin n → Fin n) → PrimeRegister n :=
  fun f => f

def PrimeValuationArithmetizationData.phiBijective {n : ℕ}
    (D : PrimeValuationArithmetizationData n) : Prop :=
  Function.Bijective D.phi

def PrimeValuationArithmetizationData.compositionLaw {n : ℕ}
    (D : PrimeValuationArithmetizationData n) : Prop :=
  ∀ M N : PrimeRegister n, D.phi (primeRegisterMul M N) = D.phi M ∘ D.phi N

set_option maxHeartbeats 400000 in
/-- Finite prime-register semigroup arithmetization: the valuation map is a bijection, and the
register product is transported to composition of coordinate functions. -/
theorem paper_killo_finite_semigroup_prime_valuation_arithmetization (n : ℕ)
    (D : PrimeValuationArithmetizationData n) : D.phiBijective ∧ D.compositionLaw := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro M N hMN
      exact hMN
    · intro f
      refine ⟨D.phiInv f, ?_⟩
      rfl
  · intro M N
    funext i
    rfl

/-- Paper label: `cor:killo-projection-idempotent-prime-register`. -/
theorem paper_killo_projection_idempotent_prime_register {n : ℕ}
    (D : PrimeValuationArithmetizationData n) (N : PrimeRegister n) :
    ((D.phi N) ∘ (D.phi N) = D.phi N) ↔ primeRegisterMul N N = N := by
  rcases paper_killo_finite_semigroup_prime_valuation_arithmetization n D with ⟨_, hcomp⟩
  constructor
  · intro h
    have hphi : D.phi (primeRegisterMul N N) = D.phi N := by
      calc
        D.phi (primeRegisterMul N N) = D.phi N ∘ D.phi N := hcomp N N
        _ = D.phi N := h
    funext i
    exact congrArg (fun f => f i) hphi
  · intro h
    calc
      D.phi N ∘ D.phi N = D.phi (primeRegisterMul N N) := by
        symm
        exact hcomp N N
      _ = D.phi N := by
        simpa using congrArg D.phi h

end Omega.Folding
