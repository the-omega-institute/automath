import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-no-inverse-limit-cylinder-parity-lift`. -/
theorem paper_conclusion_window6_no_inverse_limit_cylinder_parity_lift {X : Nat -> Type}
    (ProjectionCompatible CylinderInvolution CanonicalSheetFlipAt6 NoExtraProtocol :
      (∀ m : Nat, X m -> X m) -> Prop)
    (hobstruction :
      ∀ τ, ProjectionCompatible τ -> CylinderInvolution τ -> NoExtraProtocol τ ->
        ¬ CanonicalSheetFlipAt6 τ) :
    ¬ ∃ τ : ∀ m : Nat, X m -> X m,
      ProjectionCompatible τ ∧ CylinderInvolution τ ∧ CanonicalSheetFlipAt6 τ ∧
        NoExtraProtocol τ := by
  rintro ⟨τ, hcompatible, hinvolution, hflip, hprotocol⟩
  exact hobstruction τ hcompatible hinvolution hprotocol hflip

end Omega.Conclusion
