import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic
import Omega.EA.PrimeRegisterMonoidRealization

namespace Omega.Folding

open Omega.EA

/-- The countable prime-exponent completion restricted to the first `k + 1` axes. -/
abbrev KilloPrimeWindow (k : ℕ) := Fin (k + 1) → ℚ

/-- A finite additive register completion with `k` rational coordinates. -/
abbrev KilloFiniteRegister (k : ℕ) := Fin k → ℚ

/-- The prime-exponent realization remains faithful on the countable direct-sum model. -/
def killoPrimeExponentEmbeddingFaithful : Prop :=
  Function.Injective registerStateMap

/-- A finite `k`-register host cannot linearly realize the first `k + 1` prime axes injectively
after passing to Grothendieck completions. -/
def killoFiniteRegisterLinearizationObstructed (k : ℕ) : Prop :=
  ¬ ∃ Φ : KilloPrimeWindow k →ₗ[ℚ] KilloFiniteRegister k, Function.Injective Φ

lemma killoFiniteRegisterLinearizationObstructed_of_finrank (k : ℕ) :
    killoFiniteRegisterLinearizationObstructed k := by
  intro h
  rcases h with ⟨Φ, hΦ⟩
  have hle : Module.finrank ℚ (KilloPrimeWindow k) ≤ Module.finrank ℚ (KilloFiniteRegister k) :=
    LinearMap.finrank_le_finrank_of_injective (f := Φ) hΦ
  have hdom : Module.finrank ℚ (KilloPrimeWindow k) = k + 1 := by
    simp [KilloPrimeWindow]
  have hcod : Module.finrank ℚ (KilloFiniteRegister k) = k := by
    simp [KilloFiniteRegister]
  omega

/-- Paper-facing prime-freedom package: the prime-exponent embedding into the countable direct
sum is faithful, but every finite-register Grothendieck completion has too small a rank to host
even the first `k + 1` prime directions injectively.
    thm:killo-prime-freedom-non-finitizability -/
theorem paper_killo_prime_freedom_non_finitizability :
    killoPrimeExponentEmbeddingFaithful ∧ ∀ k : ℕ, killoFiniteRegisterLinearizationObstructed k :=
  by
  refine ⟨registerStateMap_injective, ?_⟩
  intro k
  exact killoFiniteRegisterLinearizationObstructed_of_finrank k

end Omega.Folding
