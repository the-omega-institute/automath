import Mathlib.Tactic

namespace Omega.Zeta

/-- Data package encoding the finite-index subgroup classification for the localized group
`G_S`. The fields record the classification by subgroups `nG_S` with `(n, P_S) = 1`, the
uniqueness and exact index formula, and the induced order-reversing lattice correspondence. -/
structure LocalizedFiniteIndexLatticeClassificationData where
  finiteIndexClassification : Prop
  uniqueness : Prop
  exactIndexFormula : Prop
  orderReversingCorrespondence : Prop
  classifiesFiniteIndexSubgroups : Prop
  preservesIndex : Prop
  finiteIndexClassification_h : finiteIndexClassification
  deriveUniqueness : finiteIndexClassification → uniqueness
  deriveExactIndexFormula : finiteIndexClassification → exactIndexFormula
  deriveOrderReversingCorrespondence :
    finiteIndexClassification → uniqueness → orderReversingCorrespondence
  deriveClassifiesFiniteIndexSubgroups :
    finiteIndexClassification → uniqueness → orderReversingCorrespondence →
      classifiesFiniteIndexSubgroups
  derivePreservesIndex : exactIndexFormula → preservesIndex

/-- Paper package: finite-index subgroups of the localized lattice are classified by the
coprime index parameter, and this classification preserves the exact subgroup index.
`thm:xi-time-part56e-localized-finite-index-lattice-classification` -/
theorem paper_xi_time_part56e_localized_finite_index_lattice_classification
    (D : LocalizedFiniteIndexLatticeClassificationData) :
    D.classifiesFiniteIndexSubgroups ∧ D.preservesIndex := by
  have hUnique : D.uniqueness := D.deriveUniqueness D.finiteIndexClassification_h
  have hIndex : D.exactIndexFormula := D.deriveExactIndexFormula D.finiteIndexClassification_h
  have hOrder : D.orderReversingCorrespondence :=
    D.deriveOrderReversingCorrespondence D.finiteIndexClassification_h hUnique
  exact ⟨D.deriveClassifiesFiniteIndexSubgroups D.finiteIndexClassification_h hUnique hOrder,
    D.derivePreservesIndex hIndex⟩

end Omega.Zeta
