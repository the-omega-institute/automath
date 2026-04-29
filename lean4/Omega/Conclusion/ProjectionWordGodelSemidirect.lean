import Mathlib.Data.List.Basic

namespace Omega.Conclusion

/-- The concrete code vector attached to a word by the symbol code `κ`. -/
def conclusion_projection_word_godel_semidirect_prefixedCodeVector {α : Type} (κ : α → ℕ)
    (w : List α) : List ℕ :=
  w.map κ

/-- A length shift on code vectors, included as the semidirect action by prefix padding. -/
def conclusion_projection_word_godel_semidirect_shift (n : ℕ) (v : List ℕ) : List ℕ :=
  List.replicate n 0 ++ v

/-- The semidirect multiplication on encoded words. -/
def conclusion_projection_word_godel_semidirect_mul (u v : List ℕ) : List ℕ :=
  u ++ v

/-- The Gödel projection map from words to their code vectors. -/
def conclusion_projection_word_godel_semidirect_Psi {α : Type} (κ : α → ℕ) (w : List α) :
    List ℕ :=
  conclusion_projection_word_godel_semidirect_prefixedCodeVector κ w

/-- Paper label: `prop:conclusion-projection-word-godel-semidirect`. -/
theorem paper_conclusion_projection_word_godel_semidirect {α : Type} [DecidableEq α]
    (κ : α → ℕ) (hκ : Function.Injective κ) :
    Function.Injective (conclusion_projection_word_godel_semidirect_Psi κ) ∧
      (∀ u v : List α,
        conclusion_projection_word_godel_semidirect_Psi κ (u ++ v) =
          conclusion_projection_word_godel_semidirect_mul
            (conclusion_projection_word_godel_semidirect_Psi κ u)
            (conclusion_projection_word_godel_semidirect_Psi κ v)) := by
  constructor
  · intro u v huv
    exact (List.map_injective_iff.2 hκ) huv
  · intro u v
    simp [conclusion_projection_word_godel_semidirect_Psi,
      conclusion_projection_word_godel_semidirect_prefixedCodeVector,
      conclusion_projection_word_godel_semidirect_mul]

end Omega.Conclusion
