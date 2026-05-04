import Mathlib.Tactic

namespace Omega.Conclusion

/-- Rank-one finite words with `B` choices at each of `k` levels. -/
abbrev conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word
    (B k : ℕ) : Type :=
  Fin k → Fin B

/-- The canonical rank-one Tate chart embeds a word as the zero slice of a two-slice target. -/
def conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_chart
    (B k : ℕ)
    (w : conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k) :
    conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k × Fin 2 :=
  (w, 0)

/-- Finite-model Haar-nullness: the rank-one chart occupies one of two equal slices. -/
def conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_haarNull
    (B k : ℕ) : Prop :=
  Fintype.card (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k) <
    Fintype.card (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k × Fin 2)

/-- Finite-model empty interior: the complementary slice contains a point outside the chart. -/
def conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_emptyInterior
    (B k : ℕ) : Prop :=
  ∃ p : conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k × Fin 2,
    p ∉ Set.range (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_chart B k)

/-- The rank-one zero-slice chart is not onto the two-slice target. -/
def conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_nonSurjective
    (B k : ℕ) : Prop :=
  ¬ Function.Surjective (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_chart B k)

/-- Concrete paper-facing statement for the finite-word Tate rank-one chart. -/
def conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_statement : Prop :=
  ∀ B k : ℕ, 0 < B →
    Fintype.card (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k) =
        B ^ k ∧
      conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_haarNull B k ∧
        conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_emptyInterior B k ∧
          conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_nonSurjective B k

/-- Paper label: `thm:conclusion-tate-uniaxial-entropy-saturation-rank-decoupling`. -/
theorem paper_conclusion_tate_uniaxial_entropy_saturation_rank_decoupling :
    conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_statement := by
  intro B k hB
  have hcard :
      Fintype.card (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k) =
        B ^ k := by
    simp [conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word]
  have hword_pos :
      0 < Fintype.card
        (conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k) := by
    rw [hcard]
    exact pow_pos hB k
  refine ⟨hcard, ?_, ?_, ?_⟩
  · rw [conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_haarNull]
    simp
    omega
  · let w : conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k :=
      fun _ => ⟨0, hB⟩
    refine ⟨(w, 1), ?_⟩
    intro hp
    rcases hp with ⟨v, hv⟩
    exact Fin.zero_ne_one (congrArg Prod.snd hv)
  · intro hsurj
    let w : conclusion_tate_uniaxial_entropy_saturation_rank_decoupling_word B k :=
      fun _ => ⟨0, hB⟩
    rcases hsurj (w, 1) with ⟨v, hv⟩
    exact Fin.zero_ne_one (congrArg Prod.snd hv)

end Omega.Conclusion
