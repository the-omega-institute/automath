import Mathlib.Tactic

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the type-preserving superselection package forced by the rigidity
    consequence `Aut(Γ₆) = 1`.
    cor:window6-type-superselection-autgamma6 -/
theorem paper_window6_type_superselection_autgamma6
    (gamma6Rigid typeAdjacencyAction blockDiagonalAction : Prop) (hRigid : gamma6Rigid)
    (hAction : gamma6Rigid -> typeAdjacencyAction)
    (hBlock : typeAdjacencyAction -> blockDiagonalAction) :
    typeAdjacencyAction ∧ blockDiagonalAction := by
  refine ⟨hAction hRigid, ?_⟩
  exact hBlock (hAction hRigid)

end Omega.GU
