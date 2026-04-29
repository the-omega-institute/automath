import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete data for two visible-hull kernels on the same carrier.  The kernels are
represented by the corresponding quotient relations. -/
structure conclusion_artin_visible_hull_fusion_law_data where
  carrier : Type u
  kernel_one : Setoid carrier
  kernel_two : Setoid carrier

/-- The fused kernel is the intersection of the two visible-kernel relations. -/
def conclusion_artin_visible_hull_fusion_law_jointKernel
    (D : conclusion_artin_visible_hull_fusion_law_data) : Setoid D.carrier where
  r x y := D.kernel_one.r x y ∧ D.kernel_two.r x y
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨D.kernel_one.refl x, D.kernel_two.refl x⟩
    · intro x y h
      exact ⟨D.kernel_one.symm h.1, D.kernel_two.symm h.2⟩
    · intro x y z hxy hyz
      exact ⟨D.kernel_one.trans hxy.1 hyz.1, D.kernel_two.trans hxy.2 hyz.2⟩

/-- The product image of the two quotient maps. -/
def conclusion_artin_visible_hull_fusion_law_productImage
    (D : conclusion_artin_visible_hull_fusion_law_data) : Type u :=
  {p : Quotient D.kernel_one × Quotient D.kernel_two //
    ∃ g : D.carrier, p = (Quotient.mk D.kernel_one g, Quotient.mk D.kernel_two g)}

/-- The universal map from the quotient by the fused kernel to the image in the product. -/
def conclusion_artin_visible_hull_fusion_law_universalMap
    (D : conclusion_artin_visible_hull_fusion_law_data) :
    Quotient (conclusion_artin_visible_hull_fusion_law_jointKernel D) →
      conclusion_artin_visible_hull_fusion_law_productImage D :=
  Quotient.lift
    (fun g =>
      ⟨(Quotient.mk D.kernel_one g, Quotient.mk D.kernel_two g), ⟨g, rfl⟩⟩)
    (by
      intro a b h
      apply Subtype.ext
      exact Prod.ext (Quotient.sound h.1) (Quotient.sound h.2))

/-- The fused visible hull is exactly the quotient by the intersection kernel, and this
quotient identifies with the image of the product quotient map. -/
def conclusion_artin_visible_hull_fusion_law_statement
    (D : conclusion_artin_visible_hull_fusion_law_data) : Prop :=
  Function.Bijective (conclusion_artin_visible_hull_fusion_law_universalMap D)

/-- Paper label: `thm:conclusion-artin-visible-hull-fusion-law`. -/
theorem paper_conclusion_artin_visible_hull_fusion_law
    (D : conclusion_artin_visible_hull_fusion_law_data) :
    conclusion_artin_visible_hull_fusion_law_statement D := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b =>
        have hval := congrArg Subtype.val hxy
        have h1 :
            Quotient.mk D.kernel_one a = Quotient.mk D.kernel_one b :=
          congrArg Prod.fst hval
        have h2 :
            Quotient.mk D.kernel_two a = Quotient.mk D.kernel_two b :=
          congrArg Prod.snd hval
        exact Quotient.sound ⟨Quotient.exact h1, Quotient.exact h2⟩
  · intro p
    rcases p.property with ⟨g, hg⟩
    refine ⟨Quotient.mk (conclusion_artin_visible_hull_fusion_law_jointKernel D) g, ?_⟩
    apply Subtype.ext
    simpa [conclusion_artin_visible_hull_fusion_law_universalMap] using hg.symm

end Omega.Conclusion
