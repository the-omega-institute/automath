import Mathlib.Tactic

namespace Omega.CircleDimension.CoherenceTimeLowerBound

/-- Pigeonhole: if `|α| < M`, any `f : Fin M → α` has a collision.
    thm:cdim-coherence-time-lower-bound-M-1overd -/
theorem paper_cdim_coherence_time_lower_bound
    {M : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (hM : Fintype.card α < M) (f : Fin M → α) :
    ∃ i j : Fin M, i ≠ j ∧ f i = f j := by
  have hcard : Fintype.card α < Fintype.card (Fin M) := by
    rwa [Fintype.card_fin]
  exact Fintype.exists_ne_map_eq_of_card_lt f hcard

/-- Contrapositive: `f : Fin M → α` cannot be injective if `|α| < M`.
    thm:cdim-coherence-time-lower-bound-M-1overd -/
theorem not_injective_of_card_lt
    {M : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (hM : Fintype.card α < M) (f : Fin M → α) :
    ¬ Function.Injective f := by
  obtain ⟨i, j, hne, heq⟩ := paper_cdim_coherence_time_lower_bound hM f
  intro hinj
  exact hne (hinj heq)

end Omega.CircleDimension.CoherenceTimeLowerBound
