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

end Omega.Conclusion
