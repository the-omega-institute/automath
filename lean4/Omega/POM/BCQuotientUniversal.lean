import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace Omega.POM

universe u v w

/-- Concrete data for a Beck-Chevalley quotient problem: two fiberwise label maps into a common
ambient type, together with a target quotient map that strictly coequalizes them. -/
structure BCQuotientUniversalData where
  α : Type u
  β : Type v
  γ : Type w
  leftMap : α → β
  rightMap : α → β
  quotientMap : β → γ
  strictlyCommutes : ∀ a, quotientMap (leftMap a) = quotientMap (rightMap a)

namespace BCQuotientUniversalData

/-- The fiberwise label differences that generate the BC quotient. -/
def bcGenerator (D : BCQuotientUniversalData) : D.β → D.β → Prop :=
  fun x y => ∃ a, x = D.leftMap a ∧ y = D.rightMap a

/-- The BC quotient setoid: the equivalence closure of the generating label differences. -/
def bcSetoid (D : BCQuotientUniversalData) : Setoid D.β :=
  Relation.EqvGen.setoid D.bcGenerator

/-- The concrete BC quotient. -/
abbrev BCQuotient (D : BCQuotientUniversalData) :=
  Quotient D.bcSetoid

/-- The canonical projection to the BC quotient. -/
def bcProjection (D : BCQuotientUniversalData) : D.β → D.BCQuotient :=
  Quotient.mk D.bcSetoid

/-- Any strictly commuting target quotient kills the BC generators, hence every BC relation. -/
def kernelContainedInTargetKernel (D : BCQuotientUniversalData) : Prop :=
  ∀ x y, (D.bcSetoid).r x y → D.quotientMap x = D.quotientMap y

/-- The target quotient map factors uniquely through the BC quotient. -/
def factorsThroughBCQuotient (D : BCQuotientUniversalData) : Prop :=
  ∃! f : D.BCQuotient → D.γ, ∀ x, f (D.bcProjection x) = D.quotientMap x

lemma kernelContainedInTargetKernel_of_strictlyCommutes (D : BCQuotientUniversalData) :
    D.kernelContainedInTargetKernel := by
  intro x y hxy
  change Relation.EqvGen D.bcGenerator x y at hxy
  let p : D.β → D.β → Prop := fun a b => D.quotientMap a = D.quotientMap b
  have hp : ∀ a b, D.bcGenerator a b → p a b := by
    intro a b hab
    rcases hab with ⟨t, rfl, rfl⟩
    exact D.strictlyCommutes t
  have hEqv : Equivalence p := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      rfl
    · intro a b hab
      exact hab.symm
    · intro a b c hab hbc
      exact hab.trans hbc
  exact (Equivalence.eqvGen_iff hEqv).1 (Relation.EqvGen.mono hp hxy)

lemma quotientMap_respects_bcSetoid (D : BCQuotientUniversalData) {x y : D.β}
    (hxy : (D.bcSetoid).r x y) : D.quotientMap x = D.quotientMap y :=
  D.kernelContainedInTargetKernel_of_strictlyCommutes x y hxy

/-- The descended quotient map on the BC quotient. -/
def descendedQuotientMap (D : BCQuotientUniversalData) : D.BCQuotient → D.γ :=
  Quotient.lift D.quotientMap (fun _ _ hxy => D.quotientMap_respects_bcSetoid hxy)

lemma descendedQuotientMap_factors (D : BCQuotientUniversalData) :
    ∀ x, D.descendedQuotientMap (D.bcProjection x) = D.quotientMap x := by
  intro x
  rfl

lemma factorsThroughBCQuotient_of_strictlyCommutes (D : BCQuotientUniversalData) :
    D.factorsThroughBCQuotient := by
  refine ⟨D.descendedQuotientMap, D.descendedQuotientMap_factors, ?_⟩
  intro g hg
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simpa [descendedQuotientMap, bcProjection] using hg x

end BCQuotientUniversalData

open BCQuotientUniversalData

/-- Paper label: `prop:pom-bc-quotient-universal`. -/
theorem paper_pom_bc_quotient_universal (D : BCQuotientUniversalData) :
    D.kernelContainedInTargetKernel ∧ D.factorsThroughBCQuotient := by
  exact
    ⟨D.kernelContainedInTargetKernel_of_strictlyCommutes,
      D.factorsThroughBCQuotient_of_strictlyCommutes⟩

end Omega.POM
