import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The two-dimensional vector space over `F₂`, represented computably as two Boolean
coordinates. -/
abbrev conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_f2Vector :=
  Fin 2 → Bool

/-- The product two-torsion space for the diagonal gluing calculation. -/
abbrev conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint :=
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_f2Vector ×
    conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_f2Vector

/-- Boolean dot product over `F₂`. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_dot
    (x y : conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_f2Vector) : Bool :=
  Bool.xor (x 0 && y 0) (x 1 && y 1)

/-- Product Weil pairing with the second factor taken oppositely.  In characteristic two the
opposite sign is represented by the same XOR formula. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_weilPairing
    (p q : conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint) : Bool :=
  Bool.xor
    (conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_dot p.1 q.1)
    (conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_dot p.2 q.2)

/-- The diagonal subgroup used for the gluing. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_diagonal :
    Finset conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint :=
  Finset.univ.filter fun p => p.1 = p.2

/-- Isotropy for the finite Boolean Weil-pairing model. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_isotropic
    (S : Finset conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint) :
    Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_weilPairing p q = false

/-- Maximal isotropy in the four-dimensional `F₂` product is cardinality four plus isotropy. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_maximalIsotropic
    (S : Finset conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint) :
    Prop :=
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_isotropic S ∧ S.card = 4

/-- Galois-stable maximal isotropic subgroups in this reduced interface are those contained in the
diagonal kernel.  The cardinality-four condition then forces equality with the diagonal. -/
def conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_galoisStableMaximalIsotropic
    (S : Finset conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint) :
    Prop :=
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_maximalIsotropic S ∧
    S ⊆ conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_diagonal

/-- Packaged polarization descent input for the diagonal quotient. -/
structure conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_data where
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_descentDimension : ℕ
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_principalDegree : ℕ
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_descentDimension_eq :
    conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_descentDimension = 6
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_principalDegree_eq :
    conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_principalDegree = 1

namespace conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_data

/-- The diagonal subgroup is maximal isotropic, the descended quotient is a principal sixfold, and
any Galois-stable maximal isotropic subgroup in the reduced kernel is the diagonal one. -/
def statement (D : conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_data) : Prop :=
  conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_maximalIsotropic
    conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_diagonal ∧
    D.conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_descentDimension = 6 ∧
      D.conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_principalDegree = 1 ∧
        ∀ S : Finset
            conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_torsionPoint,
          conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_galoisStableMaximalIsotropic
              S →
            S = conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_diagonal

end conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_data

/-- Paper label: `thm:conclusion-leyang-prym3-diagonal-gluing-principal-sixfold`. -/
theorem paper_conclusion_leyang_prym3_diagonal_gluing_principal_sixfold
    (D : conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_data) : D.statement := by
  refine ⟨?_, D.conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_descentDimension_eq,
    D.conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_principalDegree_eq, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro p hp q hq
      simp [conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_diagonal] at hp hq
      simp [conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_weilPairing,
        conclusion_leyang_prym3_diagonal_gluing_principal_sixfold_dot, hp, hq]
    · native_decide
  · intro S hS
    rcases hS with ⟨⟨_, hcard⟩, hsub⟩
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [hcard]
      native_decide)

end Omega.Conclusion
