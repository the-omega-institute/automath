namespace Omega.Zeta

/-- Paper label: `thm:xi-p7-q5-b5-primitive-element-degree125`. -/
theorem paper_xi_p7_q5_b5_primitive_element_degree125
    (tripleDisjoint degree125 primitiveTheta : Prop)
    (hdeg : tripleDisjoint → degree125)
    (hprim : tripleDisjoint → primitiveTheta)
    (h : tripleDisjoint) :
    degree125 ∧ primitiveTheta := by
  exact ⟨hdeg h, hprim h⟩

end Omega.Zeta
