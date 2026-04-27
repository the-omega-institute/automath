import Mathlib.Data.Fintype.Card
import Omega.Folding.FixedFiberLedgerComplexity

namespace Omega.Conclusion

open Omega

/-- Concrete input instance for the parsimonious fixed-fiber CNF reduction. -/
structure conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data where
  n : ℕ
  formula : Omega.FoldFibreThreeCNF (Fin n)

/-- Source satisfying assignments of the original three-CNF formula. -/
abbrev conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_source
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) :=
  {assignment : Fin D.n → Bool // Omega.foldFibreFormulaSatisfied assignment D.formula}

/-- Restricted fixed-fiber witnesses: exactly the encoded witnesses coming from source assignments. -/
abbrev conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_target
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) :=
  {word : Omega.FoldFibreStarWord D.n //
    ∃ assignment : Fin D.n → Bool,
      word = Omega.foldFibreStarEncode assignment ∧
        Omega.foldFibreFormulaSatisfied assignment D.formula}

/-- Forward parsimonious map from satisfying assignments to encoded fixed-fiber witnesses. -/
def conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) :
    conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_source D →
      conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_target D :=
  fun assignment =>
    ⟨Omega.foldFibreStarEncode assignment.1, assignment.1, rfl, assignment.2⟩

/-- Backward map recovering the unique source assignment from an encoded fixed-fiber witness. -/
noncomputable def conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) :
    conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_target D →
      conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_source D :=
  fun witness =>
    ⟨Classical.choose witness.2,
      (Classical.choose_spec witness.2).2⟩

/-- The concrete count-preservation and membership package for the restricted reduction. -/
noncomputable def conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_statement
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) : Prop := by
  classical
  exact
    Function.LeftInverse
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward D)
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward D) ∧
    Function.RightInverse
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward D)
      (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward D) ∧
    Fintype.card (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_target D) =
      Fintype.card (conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_source D) ∧
    (∀ assignment : Fin D.n → Bool,
      Omega.foldFibreFormulaSatisfied
          (Omega.foldFibreWordAssignment (Omega.foldFibreStarEncode assignment))
          (Omega.foldFibreLiftFormula D.formula) ↔
        Omega.foldFibreFormulaSatisfied assignment D.formula) ∧
    Omega.FoldFibre3SATNPComplete

/-- Paper label: `thm:conclusion-sharp-fiber-cnf-sharpPcomplete-parsimonious`.
The restricted encoded witnesses are in bijection with satisfying assignments of the source
three-CNF instance, so the reduction preserves the exact number of witnesses; the verifier package
is the existing fixed-fiber `#P` membership wrapper. -/
theorem paper_conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious
    (D : conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_data) :
    conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_statement D := by
  classical
  refine ⟨?_, ?_, ?_, ?_, Omega.paper_fold_fibre_3sat_np_complete⟩
  · intro assignment
    apply Subtype.ext
    dsimp [conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward,
      conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward]
    have hchosen :=
      (Classical.choose_spec
        (show ∃ source : Fin D.n → Bool,
          Omega.foldFibreStarEncode assignment.1 = Omega.foldFibreStarEncode source ∧
            Omega.foldFibreFormulaSatisfied source D.formula from
            ⟨assignment.1, rfl, assignment.2⟩)).1
    exact Omega.foldFibreStarEncode_injective D.n hchosen.symm
  · intro witness
    apply Subtype.ext
    dsimp [conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward,
      conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward]
    exact (Classical.choose_spec witness.2).1.symm
  · exact Fintype.card_congr
      { toFun := conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward D
        invFun := conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward D
        left_inv := by
          intro witness
          apply Subtype.ext
          dsimp [conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward,
            conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward]
          exact (Classical.choose_spec witness.2).1.symm
        right_inv := by
          intro assignment
          apply Subtype.ext
          dsimp [conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_backward,
            conclusion_sharp_fiber_cnf_sharppcomplete_parsimonious_forward]
          have hchosen :=
            (Classical.choose_spec
              (show ∃ source : Fin D.n → Bool,
                Omega.foldFibreStarEncode assignment.1 = Omega.foldFibreStarEncode source ∧
                  Omega.foldFibreFormulaSatisfied source D.formula from
                  ⟨assignment.1, rfl, assignment.2⟩)).1
          exact Omega.foldFibreStarEncode_injective D.n hchosen.symm }
  · intro assignment
    exact Omega.foldFibreFormulaSatisfied_lift_encode_iff assignment D.formula

end Omega.Conclusion
