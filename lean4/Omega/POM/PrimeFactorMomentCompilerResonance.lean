import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic
import Omega.POM.MomentMinreal
import Omega.POM.RmomSound

namespace Omega.POM

/-- The prefix-product fingerprint after `k` prime-factor compression steps. -/
def pom_prime_factor_moment_compiler_resonance_prefix_product (L : List ℕ) (k : ℕ) : ℕ :=
  (L.take k).prod

/-- The remaining suffix-product fingerprint after `k` prime-factor compression steps. -/
def pom_prime_factor_moment_compiler_resonance_suffix_product (L : List ℕ) (k : ℕ) : ℕ :=
  (L.drop k).prod

/-- The compiled fingerprint represented by the whole prime-factor chain. -/
def pom_prime_factor_moment_compiler_resonance_compiled_fingerprint (L : List ℕ) : ℕ :=
  L.prod

/-- Concrete data for the prime-factor moment-compiler resonance package. -/
structure pom_prime_factor_moment_compiler_resonance_data where
  rmom : pom_rmom_sound_data
  minreal : MomentMinrealData
  primeFactors : List ℕ
  prime_chain : ∀ p ∈ primeFactors, Nat.Prime p

namespace pom_prime_factor_moment_compiler_resonance_data

/-- Paper-facing statement for the prime-factor chain model: every intermediate prefix/suffix
split preserves the compiled fingerprint, the full chain collapses the residual to `1`, and the
RMOM plus minimal-realization certificates remain available along the chain. -/
def pom_prime_factor_moment_compiler_resonance_statement
    (D : pom_prime_factor_moment_compiler_resonance_data) : Prop :=
  (∀ k,
      pom_prime_factor_moment_compiler_resonance_prefix_product D.primeFactors k *
        pom_prime_factor_moment_compiler_resonance_suffix_product D.primeFactors k =
          pom_prime_factor_moment_compiler_resonance_compiled_fingerprint D.primeFactors) ∧
    pom_prime_factor_moment_compiler_resonance_prefix_product
        D.primeFactors D.primeFactors.length =
      pom_prime_factor_moment_compiler_resonance_compiled_fingerprint D.primeFactors ∧
    pom_prime_factor_moment_compiler_resonance_suffix_product
        D.primeFactors D.primeFactors.length = 1 ∧
    (∀ p ∈ D.primeFactors, Nat.Prime p) ∧
    D.rmom.pom_rmom_sound_statement ∧
    D.minreal.hankelRank = D.minreal.recurrenceOrder ∧
    D.minreal.minimalRealizationDim = D.minreal.recurrenceOrder

end pom_prime_factor_moment_compiler_resonance_data

open pom_prime_factor_moment_compiler_resonance_data

/-- Paper label: `thm:pom-prime-factor-moment-compiler-resonance`.
The prime-factor chain preserves the compiled fingerprint at every prefix/suffix split, and after
the full chain the residual collapses to `1`; together with RMOM soundness and moment/minreal this
packages the audited resonance-friendly compilation route. -/
theorem paper_pom_prime_factor_moment_compiler_resonance
    (D : Omega.POM.pom_prime_factor_moment_compiler_resonance_data) :
    D.pom_prime_factor_moment_compiler_resonance_statement := by
  have hminreal := paper_pom_moment_minreal D.minreal
  refine ⟨?_, ?_, ?_, D.prime_chain, paper_pom_rmom_sound D.rmom, hminreal.1, hminreal.2⟩
  · intro k
    simpa [pom_prime_factor_moment_compiler_resonance_prefix_product,
      pom_prime_factor_moment_compiler_resonance_suffix_product,
      pom_prime_factor_moment_compiler_resonance_compiled_fingerprint] using
      List.prod_take_mul_prod_drop D.primeFactors k
  · simp [pom_prime_factor_moment_compiler_resonance_prefix_product,
      pom_prime_factor_moment_compiler_resonance_compiled_fingerprint]
  · simp [pom_prime_factor_moment_compiler_resonance_suffix_product]

end Omega.POM
