import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6B3C3RootcloudIsotropicDesign
import Omega.Zeta.XiTimePart9zeCenterCondexpPimsnerPopaIndex

namespace Omega.Conclusion

/-- Coordinate projection for the concrete window-`6` `C₃` root table. -/
def conclusion_window6_c3_rootlength_fiber_coordinate_law_coord
    (r : Omega.GU.Weight) : Fin 3 → ℤ
  | 0 => r.1
  | 1 => r.2.1
  | 2 => r.2.2

/-- The six long `C₃` roots, recovered from the audited `B₃/C₃` root cloud by squared length. -/
def conclusion_window6_c3_rootlength_fiber_coordinate_law_longRoots :
    List Omega.GU.Weight :=
  Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_c3_roots.filter
    (fun r => decide (Omega.GU.weightNormSq r = 4))

/-- The three short-root coordinate planes, indexed by the vanishing coordinate. -/
def conclusion_window6_c3_rootlength_fiber_coordinate_law_shortRootCoordinatePlane
    (i : Fin 3) : List Omega.GU.Weight :=
  Omega.DerivedConsequences.derived_window6_b3c3_rootcloud_isotropic_design_c3_roots.filter
    (fun r =>
      decide
        (Omega.GU.weightNormSq r = 2 ∧
          conclusion_window6_c3_rootlength_fiber_coordinate_law_coord r i = 0))

/-- Zeckendorf lookup attached to the two `C₃` root lengths in the window-`6` table. -/
def conclusion_window6_c3_rootlength_fiber_coordinate_law_zeckendorfValue
    (r : Omega.GU.Weight) : ℕ :=
  if Omega.GU.weightNormSq r = 4 then Nat.fib 6
  else if Omega.GU.weightNormSq r = 2 then Nat.fib 5
  else 0

/-- Concrete statement for
`thm:conclusion-window6-c3-rootlength-fiber-coordinate-law`.

The finite audit records the six long roots, the three short-root coordinate planes,
their Zeckendorf length values, and the window-`6` fiber-degree clauses. -/
def conclusion_window6_c3_rootlength_fiber_coordinate_law_statement : Prop :=
  conclusion_window6_c3_rootlength_fiber_coordinate_law_longRoots.length = 6 ∧
    (conclusion_window6_c3_rootlength_fiber_coordinate_law_longRoots.all
        (fun r => decide (Omega.GU.weightNormSq r = 4)) =
      true) ∧
    (∀ i : Fin 3,
      (conclusion_window6_c3_rootlength_fiber_coordinate_law_shortRootCoordinatePlane i).length =
        4) ∧
    (∀ i : Fin 3,
      (conclusion_window6_c3_rootlength_fiber_coordinate_law_shortRootCoordinatePlane i).all
          (fun r =>
            decide
              (Omega.GU.weightNormSq r = 2 ∧
                conclusion_window6_c3_rootlength_fiber_coordinate_law_coord r i = 0)) =
        true) ∧
    (conclusion_window6_c3_rootlength_fiber_coordinate_law_longRoots.map
        conclusion_window6_c3_rootlength_fiber_coordinate_law_zeckendorfValue =
      [8, 8, 8, 8, 8, 8]) ∧
    (∀ i : Fin 3,
      (conclusion_window6_c3_rootlength_fiber_coordinate_law_shortRootCoordinatePlane i).map
          conclusion_window6_c3_rootlength_fiber_coordinate_law_zeckendorfValue =
        [5, 5, 5, 5]) ∧
    (∀ i : Fin 21,
      Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 2 ∨
        Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 3 ∨
          Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i =
            4) ∧
      ((Finset.univ.filter fun i : Fin 21 =>
          Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i = 2).card =
        8) ∧
        ((Finset.univ.filter fun i : Fin 21 =>
            Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i =
              3).card =
          4) ∧
          ((Finset.univ.filter fun i : Fin 21 =>
              Omega.Zeta.xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i =
                4).card =
            9)

/-- Paper label: `thm:conclusion-window6-c3-rootlength-fiber-coordinate-law`. -/
theorem paper_conclusion_window6_c3_rootlength_fiber_coordinate_law :
    conclusion_window6_c3_rootlength_fiber_coordinate_law_statement := by
  unfold conclusion_window6_c3_rootlength_fiber_coordinate_law_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide
  · intro i
    fin_cases i <;> native_decide
  · intro i
    fin_cases i <;> native_decide
  · native_decide
  · native_decide
  · native_decide

end Omega.Conclusion
