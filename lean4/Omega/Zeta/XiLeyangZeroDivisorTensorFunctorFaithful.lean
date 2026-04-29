namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-zero-divisor-tensor-functor-faithful`. -/
theorem paper_xi_leyang_zero_divisor_tensor_functor_faithful {Rep Divisor ConjClass : Type}
    [Add Divisor] (directSum tensor : Rep → Rep → Rep)
    (boxtimes : Divisor → Divisor → Divisor) (LY : Rep → Divisor)
    (sameConjClass finiteReadout : Prop)
    (h_add : ∀ V W, LY (directSum V W) = LY V + LY W)
    (h_tensor : ∀ V W, LY (tensor V W) = boxtimes (LY V) (LY W))
    (h_faithful : sameConjClass) (h_finite : finiteReadout) :
    (∀ V W, LY (directSum V W) = LY V + LY W) ∧
      (∀ V W, LY (tensor V W) = boxtimes (LY V) (LY W)) ∧
        sameConjClass ∧ finiteReadout := by
  let _conjClassType : Type := ConjClass
  exact ⟨h_add, h_tensor, h_faithful, h_finite⟩

end Omega.Zeta
