namespace Omega.Zeta

universe u

/-- Paper label: `thm:xi-p7-q5-primitive-element-degree25`. -/
theorem paper_xi_p7_q5_primitive_element_degree25
    (K12 : Type u)
    (degreeOverQ : Type u → Nat)
    (primitiveElement : K12 → Prop)
    (theta : K12)
    (linearlyDisjoint distinctConjugateSums : Prop)
    (hdisj : linearlyDisjoint)
    (hdistinct : distinctConjugateSums)
    (hdegree : linearlyDisjoint → degreeOverQ K12 = 25)
    (hprimitive : distinctConjugateSums → primitiveElement theta) :
    degreeOverQ K12 = 25 ∧ primitiveElement theta := by
  exact ⟨hdegree hdisj, hprimitive hdistinct⟩

end Omega.Zeta
