import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-transformation package capturing the basic range-cardinality stratification
used in `thm:xi-prime-register-green-rank-stratification`. -/
structure
    xi_prime_register_green_rank_stratification_XiPrimeRegisterGreenRankStratification
    (n : ℕ) where
  xi_prime_register_green_rank_stratification_rank_le_domain :
    ∀ f : Fin n → Fin n, Fintype.card (Set.range f) ≤ n
  xi_prime_register_green_rank_stratification_no_rank_above_domain :
    ∀ k : ℕ, n < k → ¬ ∃ f : Fin n → Fin n, Fintype.card (Set.range f) = k
  xi_prime_register_green_rank_stratification_rank_one_exists_iff :
    (∃ f : Fin n → Fin n, Fintype.card (Set.range f) = 1) ↔ n ≠ 0

local notation "XiPrimeRegisterGreenRankStratification" =>
  xi_prime_register_green_rank_stratification_XiPrimeRegisterGreenRankStratification

/-- Paper label: `thm:xi-prime-register-green-rank-stratification`. -/
theorem paper_xi_prime_register_green_rank_stratification (n : ℕ) :
    XiPrimeRegisterGreenRankStratification n := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro f
    simpa using Fintype.card_le_of_injective (fun x : Set.range f => x.1) (fun x y h => by
      exact Subtype.ext h)
  · intro k hk
    rintro ⟨f, hf⟩
    have hle : Fintype.card (Set.range f) ≤ n := by
      simpa using Fintype.card_le_of_injective (fun x : Set.range f => x.1) (fun x y h => by
        exact Subtype.ext h)
    exact (not_le_of_gt hk) (hf ▸ hle)
  · constructor
    · rintro ⟨f, hf⟩ hzero
      subst hzero
      simp at hf
    · intro hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let z : Fin n := ⟨0, hnpos⟩
      let f : Fin n → Fin n := fun _ => z
      refine ⟨f, ?_⟩
      have hrange : Set.range f = {z} := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          simp [f]
        · intro hy
          simp at hy
          subst hy
          exact ⟨z, by simp [f]⟩
      simp [hrange]

end Omega.Zeta
