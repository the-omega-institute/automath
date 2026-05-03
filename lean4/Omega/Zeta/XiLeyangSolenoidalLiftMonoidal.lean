namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-solenoidal-lift-monoidal`. -/
theorem paper_xi_leyang_solenoidal_lift_monoidal {Rep Div : Type}
    (LY : Rep → Div) (directSum tensor : Rep → Rep → Rep) (divAdd divConv : Div → Div → Div)
    (h_sum : ∀ V W, LY (directSum V W) = divAdd (LY V) (LY W))
    (h_tensor : ∀ V W, LY (tensor V W) = divConv (LY V) (LY W)) :
    (∀ V W, LY (directSum V W) = divAdd (LY V) (LY W)) ∧
      (∀ V W, LY (tensor V W) = divConv (LY V) (LY W)) := by
  exact ⟨h_sum, h_tensor⟩

end Omega.Zeta
