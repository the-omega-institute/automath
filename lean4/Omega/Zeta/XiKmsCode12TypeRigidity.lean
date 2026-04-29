import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-kms-code12-type-rigidity`. -/
theorem paper_xi_kms_code12_type_rigidity
    (isHyperfiniteIIIInvPhi flowWeightsCircle scaleRigid : Prop)
    (hType : isHyperfiniteIIIInvPhi)
    (hFlow : flowWeightsCircle)
    (hRigid : isHyperfiniteIIIInvPhi → flowWeightsCircle → scaleRigid) :
    isHyperfiniteIIIInvPhi ∧ flowWeightsCircle ∧ scaleRigid := by
  exact ⟨hType, hFlow, hRigid hType hFlow⟩

end Omega.Zeta
