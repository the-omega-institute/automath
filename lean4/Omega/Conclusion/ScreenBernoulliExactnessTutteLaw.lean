import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper label: `prop:conclusion-screen-bernoulli-exactness-tutte-law`. -/
theorem paper_conclusion_screen_bernoulli_exactness_tutte_law {E : Type*} [Fintype E]
    [DecidableEq E] (rank : Finset E → ℕ) (rho : ℕ) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (hcard : ∀ S : Finset E, rank S = rho → rho ≤ S.card) :
    (∑ S : Finset E,
        if rank S = rho then p ^ S.card * (1 - p) ^ (Fintype.card E - S.card) else 0) =
      p ^ rho * (1 - p) ^ (Fintype.card E - rho) *
        (∑ S : Finset E,
          if rank S = rho then (p / (1 - p)) ^ (S.card - rho) else 0) := by
  classical
  have _hp0 : 0 < p := hp0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro S _hS
  by_cases hrank : rank S = rho
  · simp only [hrank, ↓reduceIte]
    have hp_ne : (1 - p : ℝ) ≠ 0 := by linarith
    have hrho_card : rho ≤ S.card := hcard S hrank
    have hcard_univ : S.card ≤ Fintype.card E := by
      exact S.card_le_univ
    have h_exp₁ : Fintype.card E - rho =
        (Fintype.card E - S.card) + (S.card - rho) := by
      omega
    have h_exp₂ : S.card = rho + (S.card - rho) := by
      omega
    rw [h_exp₁, pow_add, div_pow, h_exp₂, pow_add]
    field_simp [hp_ne]
    simp
  · simp [hrank]

end Omega.Conclusion
