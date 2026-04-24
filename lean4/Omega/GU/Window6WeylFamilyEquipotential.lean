import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.Window6FamilyFibration15plus1

namespace Omega.GU

/-- A concrete `48`-point group model used to realize the window-6 family carrier as a regular
orbit. -/
abbrev Window6WeylModel := ZMod 16 × ZMod 3

/-- The `16`-point subgroup model underlying each boundary fiber. -/
abbrev Window6WeylFamilySubgroupModel := ZMod 16

/-- The quotient-to-boundary projection for the concrete `48 = 16 * 3` Weyl model. -/
noncomputable def window6WeylProjection : Window6WeylModel → Fin 3 :=
  fun g => (Fintype.equivFin (ZMod 3)) g.2

/-- The boundary fiber over a fixed label in the concrete Weyl model. -/
def window6WeylFiber (i : Fin 3) :=
  {g : Window6WeylModel // window6WeylProjection g = i}

noncomputable instance instFintypeWindow6WeylFiber (i : Fin 3) : Fintype (window6WeylFiber i) := by
  dsimp [window6WeylFiber, window6WeylProjection]
  infer_instance

/-- Each boundary fiber is canonically a `16`-point translate of the subgroup model. -/
noncomputable def window6WeylFiberEquiv (i : Fin 3) :
    Window6WeylFamilySubgroupModel ≃ window6WeylFiber i where
  toFun a := ⟨(a, (Fintype.equivFin (ZMod 3)).symm i), by simp [window6WeylProjection]⟩
  invFun g := g.1.1
  left_inv a := rfl
  right_inv g := by
    rcases g with ⟨⟨a, b⟩, hb⟩
    have hb' : b = (Fintype.equivFin (ZMod 3)).symm i := by
      apply (Fintype.equivFin (ZMod 3)).injective
      simpa [window6WeylProjection] using hb
    apply Subtype.ext
    simp [hb']

/-- Any two finite `48`-element models are equivalent, so transport the regular action from the
concrete Weyl model to the family carrier. -/
noncomputable def window6WeylFamilyEquiv : Window6WeylModel ≃ Window6FamilyCarrier :=
  (Fintype.equivFin Window6WeylModel).trans (Fintype.equivFin Window6FamilyCarrier).symm

/-- The transported regular action of the concrete Weyl model on the family carrier. -/
noncomputable def window6WeylTransportedAction
    (g : Window6WeylModel) (x : Window6FamilyCarrier) : Window6FamilyCarrier :=
  window6WeylFamilyEquiv (g + window6WeylFamilyEquiv.symm x)

/-- The window-6 family carrier has the same cardinality as the concrete `48`-element Weyl model,
so the regular action transports to a regular orbit; the `16`-point subgroup fibers over a
`3`-element quotient, matching the family-fibration data.
    cor:window6-weyl-family-equipotential -/
theorem paper_window6_weyl_family_equipotential :
    ∃ e : Window6WeylModel ≃ Window6FamilyCarrier,
      (∀ x y : Window6FamilyCarrier, ∃! g : Window6WeylModel, e (g + e.symm x) = y) ∧
      Fintype.card Window6WeylModel = 48 ∧
      Fintype.card Window6FamilyCarrier = 48 ∧
      Fintype.card Window6WeylFamilySubgroupModel = 16 ∧
      Fintype.card (Fin 3) = 3 ∧
      (∀ i : Fin 3, Fintype.card (window6WeylFiber i) = 16) ∧
      (∀ i : Fin 3, Fintype.card (window6FamilyFiber i) = 16) := by
  refine ⟨window6WeylFamilyEquiv, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine ⟨window6WeylFamilyEquiv.symm y - window6WeylFamilyEquiv.symm x, ?_, ?_⟩
    · simp
    · intro g hg
      have h' : g + window6WeylFamilyEquiv.symm x = window6WeylFamilyEquiv.symm y := by
        simpa using congrArg window6WeylFamilyEquiv.symm hg
      exact (eq_sub_iff_add_eq).2 h'
  · simp [Window6WeylModel]
  · exact paper_window6_family_fibration_15plus1.2
  · simp [Window6WeylFamilySubgroupModel]
  · simp
  · intro i
    simpa using (Fintype.card_congr (window6WeylFiberEquiv i)).symm
  · exact paper_window6_family_fibration_15plus1.1

end Omega.GU
