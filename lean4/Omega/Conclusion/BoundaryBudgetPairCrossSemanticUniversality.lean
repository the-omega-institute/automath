import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the shared boundary-budget pair `(r, c)`. The fields record the boundary
rank, component count, and concrete cardinalities appearing in the finite-field, torus, finite
group, and codebook semantics. -/
structure conclusion_boundary_budget_pair_cross_semantic_universality_data where
  conclusion_boundary_budget_pair_cross_semantic_universality_rank : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_componentCount : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_primeCard : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_finiteFieldFiber : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_torusTorsorRank : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_groupCard : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_codebookBaseCard : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard : ℕ
  conclusion_boundary_budget_pair_cross_semantic_universality_finiteFieldFiber_eq :
    conclusion_boundary_budget_pair_cross_semantic_universality_finiteFieldFiber =
      conclusion_boundary_budget_pair_cross_semantic_universality_primeCard ^
        conclusion_boundary_budget_pair_cross_semantic_universality_rank
  conclusion_boundary_budget_pair_cross_semantic_universality_torusTorsorRank_eq :
    conclusion_boundary_budget_pair_cross_semantic_universality_torusTorsorRank =
      conclusion_boundary_budget_pair_cross_semantic_universality_rank
  conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard_eq :
    conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard =
      conclusion_boundary_budget_pair_cross_semantic_universality_groupCard ^
        (conclusion_boundary_budget_pair_cross_semantic_universality_rank -
          conclusion_boundary_budget_pair_cross_semantic_universality_componentCount)
  conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard_eq :
    conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard =
      conclusion_boundary_budget_pair_cross_semantic_universality_codebookBaseCard *
        conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard

namespace conclusion_boundary_budget_pair_cross_semantic_universality_data

/-- The finite-field boundary fiber has cardinality `p^r`. -/
def finiteFieldFiberCard
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data) : Prop :=
  D.conclusion_boundary_budget_pair_cross_semantic_universality_finiteFieldFiber =
    D.conclusion_boundary_budget_pair_cross_semantic_universality_primeCard ^
      D.conclusion_boundary_budget_pair_cross_semantic_universality_rank

/-- The nonempty torus solution fiber is modeled by the same exponent `r`. -/
def torusTorsorStructure
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data) : Prop :=
  D.conclusion_boundary_budget_pair_cross_semantic_universality_torusTorsorRank =
    D.conclusion_boundary_budget_pair_cross_semantic_universality_rank

/-- The finite-group boundary representation groupoid has cardinality `|G|^(r-c)`. -/
def gaugeGroupoidCardinality
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data) : Prop :=
  D.conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard =
    D.conclusion_boundary_budget_pair_cross_semantic_universality_groupCard ^
      (D.conclusion_boundary_budget_pair_cross_semantic_universality_rank -
        D.conclusion_boundary_budget_pair_cross_semantic_universality_componentCount)

/-- The codebook cardinality multiplies the coarse-label count by the gauge groupoid count. -/
def codebookCardinality
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data) : Prop :=
  D.conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard =
    D.conclusion_boundary_budget_pair_cross_semantic_universality_codebookBaseCard *
      D.conclusion_boundary_budget_pair_cross_semantic_universality_groupCard ^
        (D.conclusion_boundary_budget_pair_cross_semantic_universality_rank -
          D.conclusion_boundary_budget_pair_cross_semantic_universality_componentCount)

lemma conclusion_boundary_budget_pair_cross_semantic_universality_codebook_product
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data)
    (hgauge : D.gaugeGroupoidCardinality) : D.codebookCardinality := by
  change
    D.conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard =
      D.conclusion_boundary_budget_pair_cross_semantic_universality_codebookBaseCard *
        D.conclusion_boundary_budget_pair_cross_semantic_universality_groupCard ^
          (D.conclusion_boundary_budget_pair_cross_semantic_universality_rank -
            D.conclusion_boundary_budget_pair_cross_semantic_universality_componentCount)
  change
    D.conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard =
      D.conclusion_boundary_budget_pair_cross_semantic_universality_groupCard ^
        (D.conclusion_boundary_budget_pair_cross_semantic_universality_rank -
          D.conclusion_boundary_budget_pair_cross_semantic_universality_componentCount) at hgauge
  rw [D.conclusion_boundary_budget_pair_cross_semantic_universality_codebookCard_eq]
  rw [hgauge]

end conclusion_boundary_budget_pair_cross_semantic_universality_data

open conclusion_boundary_budget_pair_cross_semantic_universality_data

/-- Paper label: `thm:conclusion-boundary-budget-pair-cross-semantic-universality`. The same
concrete pair `(r, c)` controls the finite-field fiber, torus torsor exponent, finite gauge
groupoid cardinality, and the resulting codebook product. -/
theorem paper_conclusion_boundary_budget_pair_cross_semantic_universality
    (D : conclusion_boundary_budget_pair_cross_semantic_universality_data) :
    D.finiteFieldFiberCard ∧ D.torusTorsorStructure ∧ D.gaugeGroupoidCardinality ∧
      D.codebookCardinality := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.conclusion_boundary_budget_pair_cross_semantic_universality_finiteFieldFiber_eq
  · exact D.conclusion_boundary_budget_pair_cross_semantic_universality_torusTorsorRank_eq
  · exact D.conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard_eq
  · exact conclusion_boundary_budget_pair_cross_semantic_universality_codebook_product D
      D.conclusion_boundary_budget_pair_cross_semantic_universality_gaugeGroupoidCard_eq

end Omega.Conclusion
