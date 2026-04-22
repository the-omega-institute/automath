import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiVisibleArithmeticFibonacciCofinalQuotients

namespace Omega.Zeta

/-- Primewise Euler exponent extracted from the `k`th modulus in the chain. -/
def gm_chain_profinite_euler_decomposition_primeExponent (M : ℕ → ℕ) (p k : ℕ) : ℕ :=
  (M k).factorization p

/-- Coordinatewise quotient map from the chapter-local profinite wrapper to the finite quotient
with modulus `M k`. -/
def gm_chain_profinite_euler_decomposition_quotient (M : ℕ → ℕ) (k : ℕ) :
    Zhat →+* ZMod (M k) :=
  Int.castRingHom (ZMod (M k))

/-- Kernel description of the coordinate quotient map. -/
def gm_chain_profinite_euler_decomposition_kernel (M : ℕ → ℕ) (k : ℕ) (z : Zhat) : Prop :=
  (M k : ℤ) ∣ z

/-- Chapter-local profinite Euler decomposition package: the completion is identified with the
existing Fibonacci/profinite wrapper, each modulus contributes its primewise exponents, the same
coordinate quotient map is available at every stage, and the kernel is exactly the divisibility
condition by `M k`. -/
abbrev GmChainProfiniteEulerDecompositionStatement (M : ℕ → ℕ) : Prop :=
  Nonempty (FibProfiniteCompletion ≃+* Zhat) ∧
    (∀ p k, p ^ gm_chain_profinite_euler_decomposition_primeExponent M p k ∣ M k) ∧
    (∀ p k, p ^ gm_chain_profinite_euler_decomposition_primeExponent M p k ∣ M (k + 1)) ∧
    (∀ k z,
      gm_chain_profinite_euler_decomposition_quotient M k z = (z : ZMod (M k))) ∧
    (∀ k z,
      gm_chain_profinite_euler_decomposition_quotient M k z = 0 ↔
        gm_chain_profinite_euler_decomposition_kernel M k z)

/-- Paper label: `thm:gm-chain-profinite-euler-decomposition`. -/
theorem paper_gm_chain_profinite_euler_decomposition (M : ℕ → ℕ)
    (hchain : ∀ k : ℕ, M k ∣ M (k + 1)) : GmChainProfiniteEulerDecompositionStatement M := by
  refine ⟨⟨paper_gm_fibonacci_profinite_axis⟩, ?_, ?_, ?_, ?_⟩
  · intro p k
    by_cases hp : Nat.Prime p
    · by_cases hMk : M k = 0
      · simp [gm_chain_profinite_euler_decomposition_primeExponent, hMk]
      · exact (hp.pow_dvd_iff_le_factorization hMk).2 le_rfl
    · simp [gm_chain_profinite_euler_decomposition_primeExponent,
        Nat.factorization_eq_zero_of_not_prime (M k) hp]
  · intro p k
    exact dvd_trans (by
      by_cases hp : Nat.Prime p
      · by_cases hMk : M k = 0
        · simp [gm_chain_profinite_euler_decomposition_primeExponent, hMk]
        · exact (hp.pow_dvd_iff_le_factorization hMk).2 le_rfl
      · simp [gm_chain_profinite_euler_decomposition_primeExponent,
          Nat.factorization_eq_zero_of_not_prime (M k) hp]) (hchain k)
  · intro k z
    rfl
  · intro k z
    simpa [gm_chain_profinite_euler_decomposition_quotient,
      gm_chain_profinite_euler_decomposition_kernel] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd z (M k))

end Omega.Zeta
