import Mathlib.Tactic

namespace Omega.POM

/-- Prime-core programs with an explicit bottom state are modelled as finite first-fit tables on
`Option S`. Queries use `some s`, while `none` serves as the distinguished bottom state. -/
abbrev FracPPBotProgram (S : Type) := List (Option S × Option S)

/-- First-fit evaluation for a finite table on `Option S`. -/
def evalFracPPBotProgram {S : Type} [DecidableEq S] : FracPPBotProgram S → Option S → Option S
  | [], _ => none
  | (src, dst) :: F, q => if src = q then dst else evalFracPPBotProgram F q

/-- Every prime-core program induces a partial self-map on `S` by restricting to the non-bottom
states. -/
def fracPPBotProgramToPartialMap {S : Type} [DecidableEq S] (F : FracPPBotProgram S) :
    S → Option S :=
  fun s => evalFracPPBotProgram F (some s)

/-- Canonical first-fit representative of a partial self-map, with an explicit bottom row. -/
noncomputable def canonicalFracPPBotProgram {S : Type} [Fintype S]
    (φ : S → Option S) : FracPPBotProgram S :=
  (Finset.univ.toList.map fun s => (some s, φ s)) ++ [(none, none)]

private lemma eval_map_some_of_mem {S : Type} [DecidableEq S] (φ : S → Option S) :
    ∀ {l : List S}, l.Nodup → ∀ {s : S}, s ∈ l →
      evalFracPPBotProgram (l.map fun t => (some t, φ t)) (some s) = φ s
  | [], _, _, hs => by cases hs
  | a :: l, hnodup, s, hs => by
      rcases List.nodup_cons.mp hnodup with ⟨ha, htail⟩
      rcases List.mem_cons.mp hs with rfl | hs'
      · simp [evalFracPPBotProgram]
      · have hne : a ≠ s := by
          intro has
          apply ha
          simpa [has] using hs'
        simp [evalFracPPBotProgram, hne, eval_map_some_of_mem φ htail hs']

private lemma eval_append_bottom_some {S : Type} [DecidableEq S] (F : FracPPBotProgram S) (s : S) :
    evalFracPPBotProgram (F ++ [(none, none)]) (some s) = evalFracPPBotProgram F (some s) := by
  induction F with
  | nil =>
      simp [evalFracPPBotProgram]
  | cons x xs ih =>
      by_cases hx : x.1 = some s
      · simp [evalFracPPBotProgram, hx]
      · simp [evalFracPPBotProgram, hx, ih]

private lemma canonicalFracPPBotProgram_spec {S : Type} [Fintype S] [DecidableEq S]
    (φ : S → Option S) :
    fracPPBotProgramToPartialMap (canonicalFracPPBotProgram φ) = φ := by
  funext s
  unfold fracPPBotProgramToPartialMap canonicalFracPPBotProgram
  rw [eval_append_bottom_some]
  exact eval_map_some_of_mem φ (Finset.nodup_toList (s := Finset.univ)) (by
    exact Finset.mem_toList.mpr (Finset.mem_univ s))

/-- Finite first-fit prime-core tables with an explicit bottom state present every partial
self-map on a finite set. The canonical representative uses at most one row per state, plus the
bottom row.
    thm:pom-fractran-primecore-finite-partial-function-category -/
theorem paper_pom_fractran_primecore_finite_partial_function_category
    (S : Type) [Fintype S] [DecidableEq S] :
    ∃ Θ : FracPPBotProgram S → (S → Option S), Function.Surjective Θ ∧
      ∀ φ : S → Option S, ∃ F, Θ F = φ ∧ F.length ≤ Fintype.card S + 1 := by
  classical
  refine ⟨fracPPBotProgramToPartialMap, ?_, ?_⟩
  · intro φ
    refine ⟨canonicalFracPPBotProgram φ, canonicalFracPPBotProgram_spec φ⟩
  · intro φ
    refine ⟨canonicalFracPPBotProgram φ, canonicalFracPPBotProgram_spec φ, ?_⟩
    simp [canonicalFracPPBotProgram]

end Omega.POM
