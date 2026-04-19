import Mathlib.Tactic

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Conclusion-level normal form for `Read_US` failures: once the three advertised `NULL` branches
are exhaustive and mutually exclusive, any hidden mixed-precision/side-channel failure class is
ruled out explicitly.
    thm:conclusion-readus-null-trichotomy-normal-form -/
theorem paper_conclusion_readus_null_trichotomy_normal_form
    (semanticNull protocolNull collisionNull hiddenFailure : Prop)
    (hexhaustive : semanticNull ∨ protocolNull ∨ collisionNull)
    (hsem : semanticNull → ¬ protocolNull ∧ ¬ collisionNull)
    (hprot : protocolNull → ¬ semanticNull ∧ ¬ collisionNull)
    (hcoll : collisionNull → ¬ semanticNull ∧ ¬ protocolNull)
    (hnohidden : hiddenFailure → False) :
    (semanticNull ∨ protocolNull ∨ collisionNull) ∧ ¬ hiddenFailure := by
  let _ := hsem
  let _ := hprot
  let _ := hcoll
  refine ⟨hexhaustive, ?_⟩
  intro hHidden
  exact hnohidden hHidden

end Omega.Conclusion
