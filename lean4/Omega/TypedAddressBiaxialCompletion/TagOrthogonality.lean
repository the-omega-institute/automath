import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.BudgetOrthogonality
import Omega.TypedAddressBiaxialCompletion.NullExhaustive

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete failure tags for the typed-address biaxial-completion chapter. -/
inductive TagWitness
  | out
  | cech
  | hard
  deriving DecidableEq

/-- Concrete chapter-local package witnessing that a single failure event carries exactly one of
the three typed tags, while also remembering the existing orthogonality interfaces used in the
surrounding section. -/
structure TagOrthogonalityData where
  budgetData : BudgetOrthogonalityData
  nullData : TypedAddressNullTrichotomyData
  witness : TagWitness
  outTag : Prop
  cechTag : Prop
  hardTag : Prop
  outTag_iff : outTag ↔ witness = .out
  cechTag_iff : cechTag ↔ witness = .cech
  hardTag_iff : hardTag ↔ witness = .hard

/-- Paper: `prop:typed-address-biaxial-completion-tag-orthogonality`. -/
theorem paper_typed_address_biaxial_completion_tag_orthogonality (h : TagOrthogonalityData) :
    (h.outTag -> ¬ h.cechTag ∧ ¬ h.hardTag) ∧
      (h.cechTag -> ¬ h.outTag ∧ ¬ h.hardTag) ∧
      (h.hardTag -> ¬ h.outTag ∧ ¬ h.cechTag) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hout
    refine ⟨?_, ?_⟩
    · intro hcech
      cases (h.outTag_iff.mp hout).symm.trans (h.cechTag_iff.mp hcech)
    · intro hhard
      cases (h.outTag_iff.mp hout).symm.trans (h.hardTag_iff.mp hhard)
  · intro hcech
    refine ⟨?_, ?_⟩
    · intro hout
      cases (h.cechTag_iff.mp hcech).symm.trans (h.outTag_iff.mp hout)
    · intro hhard
      cases (h.cechTag_iff.mp hcech).symm.trans (h.hardTag_iff.mp hhard)
  · intro hhard
    refine ⟨?_, ?_⟩
    · intro hout
      cases (h.hardTag_iff.mp hhard).symm.trans (h.outTag_iff.mp hout)
    · intro hcech
      cases (h.hardTag_iff.mp hhard).symm.trans (h.cechTag_iff.mp hcech)

end Omega.TypedAddressBiaxialCompletion
