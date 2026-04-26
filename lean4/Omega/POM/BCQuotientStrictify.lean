import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic
import Omega.POM.BCQuotientUniversal

namespace Omega.POM

open BCQuotientUniversalData

/-- A visible observable is fixed by the strictified conditional expectation exactly when it
descends along the BC quotient projection. -/
def pom_bc_quotient_strictify_fixed_by_condexp
    (D : BCQuotientUniversalData) {A : Type*} (f : D.β → A) : Prop :=
  ∃ g : D.BCQuotient → A, ∀ x, g (D.bcProjection x) = f x

/-- The anomaly carried by a visible observable is the difference between two related labels. -/
def pom_bc_quotient_strictify_visible_anomaly
    (D : BCQuotientUniversalData) {A : Type*} [AddGroup A] (f : D.β → A) (x y : D.β) : A :=
  f x - f y

/-- Paper label: `prop:pom-bc-quotient-strictify`. Every strictly commuting BC quotient comes with
its descended visible label, every visible character is fixed by the quotient conditional
expectation, and the induced anomaly vanishes on BC-related labels. -/
theorem paper_pom_bc_quotient_strictify
    {α β γ A : Type*} [AddGroup A]
    (leftMap rightMap : α → β) (quotientMap : β → γ)
    (strictlyCommutes : ∀ a, quotientMap (leftMap a) = quotientMap (rightMap a)) :
    let D : BCQuotientUniversalData :=
      { α := α
        β := β
        γ := γ
        leftMap := leftMap
        rightMap := rightMap
        quotientMap := quotientMap
        strictlyCommutes := strictlyCommutes }
    ∃ visibleLabel : D.BCQuotient → γ,
      (∀ x, visibleLabel (D.bcProjection x) = quotientMap x) ∧
      (∀ χ : γ → A,
        pom_bc_quotient_strictify_fixed_by_condexp D (fun x => χ (quotientMap x))) ∧
      (∀ χ : γ → A, ∀ x y, (D.bcSetoid).r x y →
        pom_bc_quotient_strictify_visible_anomaly D (fun t => χ (quotientMap t)) x y = 0) ∧
      D.kernelContainedInTargetKernel ∧
      D.factorsThroughBCQuotient := by
  dsimp
  let D : BCQuotientUniversalData :=
    { α := α
      β := β
      γ := γ
      leftMap := leftMap
      rightMap := rightMap
      quotientMap := quotientMap
      strictlyCommutes := strictlyCommutes }
  refine ⟨D.descendedQuotientMap, D.descendedQuotientMap_factors, ?_, ?_,
    D.kernelContainedInTargetKernel_of_strictlyCommutes,
    D.factorsThroughBCQuotient_of_strictlyCommutes⟩
  · intro χ
    refine ⟨fun q => χ (D.descendedQuotientMap q), ?_⟩
    intro x
    exact congrArg χ (D.descendedQuotientMap_factors x)
  · intro χ x y hxy
    have hq : quotientMap x = quotientMap y := D.quotientMap_respects_bcSetoid hxy
    simp [pom_bc_quotient_strictify_visible_anomaly, hq]

end Omega.POM
