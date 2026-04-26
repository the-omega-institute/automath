import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

universe u

/-- Concrete data for the graph-homology obstruction package: a finite graph skeleton, a finite
cycle space with an integral weight cocycle, a finite torsion quotient, and the resonant character
group identified with that quotient by the supplied Smith/torsion equivalence. -/
structure gm_resonant_character_group_homology_data where
  vertex : Type u
  edge : Type u
  [vertexFintype : Fintype vertex]
  [edgeFintype : Fintype edge]
  cycleSpace : Type u
  [cycleAddCommGroup : AddCommGroup cycleSpace]
  [cycleFintype : Fintype cycleSpace]
  weightCocycle : cycleSpace →+ ℤ
  torsionQuotient : Type u
  [torsionCommGroup : CommGroup torsionQuotient]
  [torsionFintype : Fintype torsionQuotient]
  resonantCharacterGroup : Type u
  [resonantCommGroup : CommGroup resonantCharacterGroup]
  smithTorsionEquiv : resonantCharacterGroup ≃* torsionQuotient
  invariantFactors : List ℕ
  invariantFactors_prod_eq_torsion_card :
    invariantFactors.prod = Fintype.card torsionQuotient

/-- The resonant character group inherits finiteness and the Smith invariant-factor cardinality
from the torsion quotient. -/
def gm_resonant_character_group_homology_statement
    (D : gm_resonant_character_group_homology_data) : Prop :=
  letI : CommGroup D.torsionQuotient := D.torsionCommGroup
  letI : Fintype D.torsionQuotient := D.torsionFintype
  letI : CommGroup D.resonantCharacterGroup := D.resonantCommGroup
  letI : Fintype D.resonantCharacterGroup :=
    Fintype.ofEquiv D.torsionQuotient D.smithTorsionEquiv.symm.toEquiv
  Nonempty (CommGroup D.resonantCharacterGroup) ∧
    Nonempty (Fintype D.resonantCharacterGroup) ∧
      Fintype.card D.resonantCharacterGroup = Fintype.card D.torsionQuotient ∧
        D.invariantFactors.prod = Fintype.card D.resonantCharacterGroup

/-- Paper label: `thm:gm-resonant-character-group-homology`. -/
theorem paper_gm_resonant_character_group_homology
    (D : gm_resonant_character_group_homology_data) :
    gm_resonant_character_group_homology_statement D := by
  letI : CommGroup D.torsionQuotient := D.torsionCommGroup
  letI : Fintype D.torsionQuotient := D.torsionFintype
  letI : CommGroup D.resonantCharacterGroup := D.resonantCommGroup
  letI : Fintype D.resonantCharacterGroup :=
    Fintype.ofEquiv D.torsionQuotient D.smithTorsionEquiv.symm.toEquiv
  dsimp [gm_resonant_character_group_homology_statement]
  refine ⟨⟨D.resonantCommGroup⟩, ⟨Fintype.ofEquiv D.torsionQuotient
    D.smithTorsionEquiv.symm.toEquiv⟩, ?_, ?_⟩
  · exact Fintype.card_congr D.smithTorsionEquiv.toEquiv
  · rw [D.invariantFactors_prod_eq_torsion_card]
    exact (Fintype.card_congr D.smithTorsionEquiv.toEquiv).symm

end Omega.SyncKernelRealInput
