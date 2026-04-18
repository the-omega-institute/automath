import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The concrete unitary-slice gate indexed by `d`: on the arithmetic side it acts by
scalar multiplication on the phase parameter. -/
def tauMap (d : ℕ) : ℕ → ℕ :=
  fun x => d * x

/-- The canonical prime normal form attached to a factorization profile. -/
def tauPrimeNormalForm (f : ℕ →₀ ℕ) : ℕ → ℕ :=
  tauMap (f.prod (· ^ ·))

lemma tauMap_mul (m n : ℕ) : tauMap (m * n) = tauMap m ∘ tauMap n := by
  funext x
  simp [tauMap, Function.comp, Nat.mul_assoc]

theorem tauMap_injective : Function.Injective tauMap := by
  intro d e h
  have h1 := congrArg (fun f => f 1) h
  simpa [tauMap] using h1

/-- Paper-facing wrapper for the unitary-slice prime normal form: `tau` is multiplicative under
composition, injective on positive indices, and the canonical normal form is exactly the prime
factorization of `d`.
    thm:unitary-slice-tau-prime-normal-form -/
theorem paper_unitary_slice_tau_prime_normal_form (d : Nat) (hd : 0 < d) :
    (∀ m n : ℕ, tauMap (m * n) = tauMap m ∘ tauMap n) ∧
    Function.Injective tauMap ∧
    tauMap d = tauPrimeNormalForm d.factorization ∧
    (∀ f : ℕ →₀ ℕ, (∀ p ∈ f.support, Nat.Prime p) →
      tauMap d = tauPrimeNormalForm f → f = d.factorization) := by
  refine ⟨tauMap_mul, tauMap_injective, ?_, ?_⟩
  · funext x
    simp [tauPrimeNormalForm, tauMap, Nat.factorization_prod_pow_eq_self hd.ne']
  · intro f hf hEq
    have hprod : f.prod (· ^ ·) = d := by
      have h1 := congrArg (fun g => g 1) hEq
      simpa [tauPrimeNormalForm, tauMap] using h1.symm
    exact (Nat.eq_factorization_iff hd.ne' hf).2 hprod

end Omega.UnitCirclePhaseArithmetic
