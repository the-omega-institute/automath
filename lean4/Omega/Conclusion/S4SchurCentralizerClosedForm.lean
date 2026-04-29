import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.S4HodgeDeterminesFixedpointCounts

open scoped BigOperators

namespace Omega.Conclusion

/-- The four nontrivial irreducible `S₄` summands visible in the Hodge package. -/
inductive conclusion_s4_schur_centralizer_closed_form_irrep
  | sgn
  | v2
  | v3
  | v3prime
  deriving DecidableEq, Fintype

/-- The multiplicities of the irreducible `S₄` summands in the Hodge decomposition. -/
def conclusion_s4_schur_centralizer_closed_form_multiplicity :
    conclusion_s4_schur_centralizer_closed_form_irrep → ℕ
  | .sgn => 5
  | .v2 => 4
  | .v3 => 3
  | .v3prime => 9

/-- The matrix block contributed by a single `S₄`-isotypic summand. -/
abbrev conclusion_s4_schur_centralizer_closed_form_block
    (ρ : conclusion_s4_schur_centralizer_closed_form_irrep) :=
  Fin (conclusion_s4_schur_centralizer_closed_form_multiplicity ρ) ×
    Fin (conclusion_s4_schur_centralizer_closed_form_multiplicity ρ)

/-- The full Schur centralizer is the disjoint union of the matrix blocks attached to each
isotypic summand. -/
abbrev conclusion_s4_schur_centralizer_closed_form_block_decomposition :=
  Σ ρ : conclusion_s4_schur_centralizer_closed_form_irrep,
    conclusion_s4_schur_centralizer_closed_form_block ρ

/-- Concrete statement package for the closed-form `S₄` Schur centralizer. -/
def conclusion_s4_schur_centralizer_closed_form_statement : Prop :=
  conclusion_s4_hodge_determines_fixedpoint_counts_statement ∧
    conclusion_s4_schur_centralizer_closed_form_multiplicity .sgn = 5 ∧
    conclusion_s4_schur_centralizer_closed_form_multiplicity .v2 = 4 ∧
    conclusion_s4_schur_centralizer_closed_form_multiplicity .v3 = 3 ∧
    conclusion_s4_schur_centralizer_closed_form_multiplicity .v3prime = 9 ∧
    (∀ c,
      conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character c =
        conclusion_s4_schur_centralizer_closed_form_multiplicity .sgn *
            conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character c +
          conclusion_s4_schur_centralizer_closed_form_multiplicity .v2 *
            conclusion_s4_hodge_determines_fixedpoint_counts_v2_character c +
          conclusion_s4_schur_centralizer_closed_form_multiplicity .v3 *
            conclusion_s4_hodge_determines_fixedpoint_counts_v3_character c +
          conclusion_s4_schur_centralizer_closed_form_multiplicity .v3prime *
            conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character c) ∧
    Fintype.card conclusion_s4_schur_centralizer_closed_form_block_decomposition =
      ∑ ρ : conclusion_s4_schur_centralizer_closed_form_irrep,
        conclusion_s4_schur_centralizer_closed_form_multiplicity ρ ^ 2 ∧
    Fintype.card conclusion_s4_schur_centralizer_closed_form_block_decomposition = 131

/-- Paper label: `thm:conclusion-s4-schur-centralizer-closed-form`. The already formalized Hodge
character has multiplicities `(5,4,3,9)`, so Schur's lemma splits the commutant into four full
matrix blocks of sizes `5`, `4`, `3`, and `9`; the resulting centralizer dimension is
`5^2 + 4^2 + 3^2 + 9^2 = 131`. -/
theorem paper_conclusion_s4_schur_centralizer_closed_form :
    conclusion_s4_schur_centralizer_closed_form_statement := by
  refine ⟨paper_conclusion_s4_hodge_determines_fixedpoint_counts, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro c
    cases c <;>
      norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
        conclusion_s4_schur_centralizer_closed_form_multiplicity,
        conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
        conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character]
  · native_decide
  · native_decide

end Omega.Conclusion
