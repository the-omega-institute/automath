import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite normal-form wrapper for rejection outputs: every run lands in one of the three `NULL`
classes or one of the three orthogonal defect-budget classes.
    cor:conclusion-reject-null-finite-normal-form -/
theorem paper_conclusion_reject_null_finite_normal_form
    (semanticNull protocolNull collisionNull defRad defDepth defEndpoint : Prop)
    (hnull : semanticNull ∨ protocolNull ∨ collisionNull)
    (hdef : defRad ∨ defDepth ∨ defEndpoint)
    (hsem : semanticNull → ¬ protocolNull ∧ ¬ collisionNull)
    (hprot : protocolNull → ¬ semanticNull ∧ ¬ collisionNull)
    (hcoll : collisionNull → ¬ semanticNull ∧ ¬ protocolNull)
    (hrad : defRad → ¬ defDepth ∧ ¬ defEndpoint)
    (hdepth : defDepth → ¬ defRad ∧ ¬ defEndpoint)
    (hend : defEndpoint → ¬ defRad ∧ ¬ defDepth) :
    semanticNull ∨ protocolNull ∨ collisionNull ∨ defRad ∨ defDepth ∨ defEndpoint := by
  let _ := hdef
  let _ := hsem
  let _ := hprot
  let _ := hcoll
  let _ := hrad
  let _ := hdepth
  let _ := hend
  rcases hnull with hSemantic | hProtocol | hCollision
  · exact Or.inl hSemantic
  · exact Or.inr <| Or.inl hProtocol
  · exact Or.inr <| Or.inr <| Or.inl hCollision

end Omega.Conclusion
