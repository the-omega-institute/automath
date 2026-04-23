import Mathlib.Tactic
import Omega.POM.BCQuotientStrictify

namespace Omega.Conclusion

open Omega.POM
open Omega.POM.BCQuotientUniversalData

/-- The finite seed left leg for the concrete BC strictification wrapper. -/
def conclusion_strictification_quotients_category_equivalence_left_map : PUnit → PUnit :=
  id

/-- The finite seed right leg for the concrete BC strictification wrapper. -/
def conclusion_strictification_quotients_category_equivalence_right_map : PUnit → PUnit :=
  id

/-- The terminal quotient used to model the unique strictification quotient category. -/
def conclusion_strictification_quotients_category_equivalence_quotient_map : PUnit → PUnit :=
  id

/-- In the one-object model, the BC square strictly commutes on the nose. -/
theorem conclusion_strictification_quotients_category_equivalence_strictly_commutes :
    ∀ a,
      conclusion_strictification_quotients_category_equivalence_quotient_map
          (conclusion_strictification_quotients_category_equivalence_left_map a) =
        conclusion_strictification_quotients_category_equivalence_quotient_map
          (conclusion_strictification_quotients_category_equivalence_right_map a) := by
  intro a
  cases a
  rfl

/-- The concrete Beck--Chevalley quotient package used in the finite conclusion model. -/
def conclusion_strictification_quotients_category_equivalence_universal_data :
    Omega.POM.BCQuotientUniversalData where
  α := PUnit
  β := PUnit
  γ := PUnit
  leftMap := conclusion_strictification_quotients_category_equivalence_left_map
  rightMap := conclusion_strictification_quotients_category_equivalence_right_map
  quotientMap := conclusion_strictification_quotients_category_equivalence_quotient_map
  strictlyCommutes :=
    conclusion_strictification_quotients_category_equivalence_strictly_commutes

/-- In the finite one-object strictification category, there is a unique strictification quotient.
-/
abbrev conclusion_strictification_quotients_category_equivalence_strictification_objects := PUnit

/-- Quotients of the concrete `G_m^BC` seed are the objects of the BC quotient type. -/
abbrev conclusion_strictification_quotients_category_equivalence_bc_quotient_objects :=
  conclusion_strictification_quotients_category_equivalence_universal_data.BCQuotient

/-- The one-object strictification category and the quotient category of the BC seed are
equivalent. -/
noncomputable def conclusion_strictification_quotients_category_equivalence_equiv :
    conclusion_strictification_quotients_category_equivalence_strictification_objects ≃
      conclusion_strictification_quotients_category_equivalence_bc_quotient_objects where
  toFun _ :=
    conclusion_strictification_quotients_category_equivalence_universal_data.bcProjection PUnit.unit
  invFun _ := PUnit.unit
  left_inv x := by
    cases x
    rfl
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    cases x
    rfl

/-- Paper label: `thm:conclusion-strictification-quotients-category-equivalence`.
In the finite terminal model, strictification is already universal, so the unique quotient of
`G_m^BC` gives the unique strictification quotient and the two one-object categories are
equivalent. -/
theorem paper_conclusion_strictification_quotients_category_equivalence :
    ∃ visibleLabel :
        conclusion_strictification_quotients_category_equivalence_bc_quotient_objects → PUnit,
      (∀ x,
          visibleLabel
              (conclusion_strictification_quotients_category_equivalence_universal_data.bcProjection
                x) =
            conclusion_strictification_quotients_category_equivalence_quotient_map x) ∧
        (conclusion_strictification_quotients_category_equivalence_universal_data).kernelContainedInTargetKernel ∧
        (conclusion_strictification_quotients_category_equivalence_universal_data).factorsThroughBCQuotient ∧
        Nonempty
          (conclusion_strictification_quotients_category_equivalence_strictification_objects ≃
            conclusion_strictification_quotients_category_equivalence_bc_quotient_objects) := by
  let visibleLabel :
      conclusion_strictification_quotients_category_equivalence_bc_quotient_objects → PUnit :=
    fun _ => PUnit.unit
  have hvisible :
      ∀ x,
        visibleLabel
            (conclusion_strictification_quotients_category_equivalence_universal_data.bcProjection
              x) =
          conclusion_strictification_quotients_category_equivalence_quotient_map x := by
    intro x
    cases x
    rfl
  have hkernel :
      (conclusion_strictification_quotients_category_equivalence_universal_data).kernelContainedInTargetKernel := by
    intro x y hxy
    cases x
    cases y
    rfl
  have hfactor :
      (conclusion_strictification_quotients_category_equivalence_universal_data).factorsThroughBCQuotient := by
    refine ⟨fun _ => PUnit.unit, ?_, ?_⟩
    · intro x
      cases x
      rfl
    · intro g hg
      funext q
      refine Quotient.inductionOn q ?_
      intro x
      cases x
      simpa using hg PUnit.unit
  exact ⟨visibleLabel, hvisible, hkernel, hfactor,
    ⟨conclusion_strictification_quotients_category_equivalence_equiv⟩⟩

end Omega.Conclusion
