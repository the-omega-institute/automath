import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-scalekernel-tree-third-order-blindness`.

If a protocol factors through observations and the real and proxy objects have the same
observation, then the protocol outputs are equal.  Any claimed faithful separator between the two
outputs is therefore impossible. -/
theorem paper_conclusion_scalekernel_tree_third_order_blindness {Obj Obs Out : Type*}
    (P : Obj → Out) (O : Obj → Obs) (real proxy : Obj)
    (hfactor : ∃ Q : Obs → Out, ∀ x, P x = Q (O x)) (hobs : O real = O proxy)
    (Faithful : Out → Prop) (hseparates : Faithful (P real) → ¬ Faithful (P proxy)) :
    P real = P proxy ∧ ¬ Faithful (P real) := by
  rcases hfactor with ⟨Q, hQ⟩
  have hsame : P real = P proxy := by
    rw [hQ real, hQ proxy, hobs]
  refine ⟨hsame, ?_⟩
  intro hfaith
  exact hseparates hfaith (hsame ▸ hfaith)

/-- Paper label:
`thm:conclusion-scalekernel-finite-shell-fourth-order-obstruction`. -/
theorem paper_conclusion_scalekernel_finite_shell_fourth_order_obstruction
    (finite_shell_deconvolution variance_formula fourth_cumulant_formula odd_cumulants_vanish
      fourth_order_first_obstruction : Prop)
    (hDeconv : finite_shell_deconvolution) (hVar : variance_formula)
    (hK4 : fourth_cumulant_formula) (hOdd : odd_cumulants_vanish)
    (hFirst :
      finite_shell_deconvolution ->
        variance_formula -> fourth_cumulant_formula -> odd_cumulants_vanish ->
          fourth_order_first_obstruction) :
    finite_shell_deconvolution ∧ variance_formula ∧ fourth_cumulant_formula ∧
      odd_cumulants_vanish ∧ fourth_order_first_obstruction := by
  exact ⟨hDeconv, hVar, hK4, hOdd, hFirst hDeconv hVar hK4 hOdd⟩

end Omega.Conclusion
