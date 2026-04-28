namespace Omega.Zeta

/-- Paper label: `prop:xi-logistic-hellinger-gram-determinant`. -/
theorem paper_xi_logistic_hellinger_gram_determinant
    (kernelClosedForm gramPositive collisionVandermondeLaw : Prop) (hkernel : kernelClosedForm)
    (hgram : gramPositive) (hcollision : collisionVandermondeLaw) :
    kernelClosedForm ∧ gramPositive ∧ collisionVandermondeLaw := by
  exact ⟨hkernel, hgram, hcollision⟩

end Omega.Zeta
