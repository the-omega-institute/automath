namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for character-theoretic detection of the intrinsic visible quotient.
    thm:intrinsic-visible-quotient -/
theorem paper_gluing_failure_intrinsic_visible_quotient
    (classAdmissible evalAnnihilator annihilator kernelIntersection quotientIdentification : Prop)
    (hDetect : classAdmissible ↔ evalAnnihilator)
    (hAnn : evalAnnihilator ↔ annihilator)
    (hKernel : annihilator → kernelIntersection)
    (hQuot : kernelIntersection → quotientIdentification) :
    (classAdmissible ↔ evalAnnihilator) ∧
      (evalAnnihilator ↔ annihilator) ∧
      (classAdmissible ↔ annihilator) ∧
      (annihilator → kernelIntersection) ∧
      (annihilator → quotientIdentification) := by
  refine ⟨hDetect, hAnn, hDetect.trans hAnn, hKernel, ?_⟩
  intro h
  exact hQuot (hKernel h)

end Omega.Topos
