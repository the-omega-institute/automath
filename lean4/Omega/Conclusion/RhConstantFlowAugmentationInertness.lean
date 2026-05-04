import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-rh-constant-flow-augmentation-inertness`. -/
theorem paper_conclusion_rh_constant_flow_augmentation_inertness
    {Obj Sentence ConstSentence : Type*} (eval : Obj → Sentence → Prop)
    (evalConst : Obj → ConstSentence → Prop) (eraseConst : ConstSentence → Sentence)
    (rhTruth : Obj → Bool) (Xpos Xneg : Obj) (hOld : ∀ φ, eval Xpos φ ↔ eval Xneg φ)
    (hConst : ∀ X ψ, evalConst X ψ ↔ eval X (eraseConst ψ))
    (hRhSep : rhTruth Xpos ≠ rhTruth Xneg) :
    ∀ ψ, evalConst Xpos ψ ↔ evalConst Xneg ψ := by
  let _hRhSep : rhTruth Xpos ≠ rhTruth Xneg := hRhSep
  intro ψ
  rw [hConst Xpos ψ, hConst Xneg ψ]
  exact hOld (eraseConst ψ)

end Omega.Conclusion
