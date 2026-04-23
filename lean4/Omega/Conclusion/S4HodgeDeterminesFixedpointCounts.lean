import Mathlib.Tactic

namespace Omega.Conclusion

/-- The four nontrivial conjugacy classes of `S₄` used in the fixed-point computation. -/
inductive conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class
  | transposition
  | doubleTransposition
  | threeCycle
  | fourCycle
  deriving DecidableEq

/-- Sign-character values on the nontrivial `S₄` conjugacy classes. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | .transposition => -1
  | .doubleTransposition => 1
  | .threeCycle => 1
  | .fourCycle => -1

/-- Values of the `2`-dimensional irreducible character on the nontrivial `S₄` conjugacy classes.
-/
def conclusion_s4_hodge_determines_fixedpoint_counts_v2_character :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | .transposition => 0
  | .doubleTransposition => 2
  | .threeCycle => -1
  | .fourCycle => 0

/-- Values of the standard `3`-dimensional irreducible character on the nontrivial `S₄`
conjugacy classes. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_v3_character :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | .transposition => 1
  | .doubleTransposition => -1
  | .threeCycle => 0
  | .fourCycle => -1

/-- Values of the twisted `3`-dimensional irreducible character on the nontrivial `S₄`
conjugacy classes. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | .transposition => -1
  | .doubleTransposition => -1
  | .threeCycle => 0
  | .fourCycle => 1

/-- Character of `V = 5·sgn ⊕ 4·V₂ ⊕ 3·V₃ ⊕ 9·V₃'` on the four nontrivial conjugacy classes. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | c =>
      5 * conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character c +
        4 * conclusion_s4_hodge_determines_fixedpoint_counts_v2_character c +
          3 * conclusion_s4_hodge_determines_fixedpoint_counts_v3_character c +
            9 * conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character c

/-- Holomorphic Lefschetz fixed-point count `2 - 2χ_V(g)` for the concrete genus-`49`
`S₄`-Hurwitz curve. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz :
    conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ
  | c => 2 - 2 * conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character c

/-- Concrete conclusion package for the `S₄` Hodge-character fixed-point computation. -/
def conclusion_s4_hodge_determines_fixedpoint_counts_statement : Prop :=
  let fix := conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz
  fix .transposition = 24 ∧
    fix .doubleTransposition = 0 ∧
      fix .threeCycle = 0 ∧
        fix .fourCycle = 0 ∧
          ∀ F :
              conclusion_s4_hodge_determines_fixedpoint_counts_conjugacy_class → ℤ,
            (∀ c,
              F c =
                2 - 2 * conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character c) →
              F .transposition = 24 ∧
                F .doubleTransposition = 0 ∧
                  F .threeCycle = 0 ∧
                    F .fourCycle = 0

/-- Paper label: `thm:conclusion-s4-hodge-determines-fixedpoint-counts`. The explicit
character values of `V = 5·sgn ⊕ 4·V₂ ⊕ 3·V₃ ⊕ 9·V₃'` give
`χ_V(τ) = -11` and `χ_V(δ) = χ_V(σ₃) = χ_V(σ₄) = 1`; applying the holomorphic Lefschetz formula
`#Fix(g) = 2 - 2χ_V(g)` yields the fixed-point counts on every nontrivial conjugacy class. -/
theorem paper_conclusion_s4_hodge_determines_fixedpoint_counts :
    conclusion_s4_hodge_determines_fixedpoint_counts_statement := by
  dsimp [conclusion_s4_hodge_determines_fixedpoint_counts_statement]
  refine ⟨by norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character],
    by norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character],
    by norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character],
    by norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character],
    ?_⟩
  intro F hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] using
      hF .transposition
  · simpa [conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] using
      hF .doubleTransposition
  · simpa [conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] using
      hF .threeCycle
  · simpa [conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
      conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character] using
      hF .fourCycle

end Omega.Conclusion
