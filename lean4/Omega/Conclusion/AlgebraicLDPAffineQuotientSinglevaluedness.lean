import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-algebraic-ldp-affine-quotient-singlevaluedness`. -/
theorem paper_conclusion_algebraic_ldp_affine_quotient_singlevaluedness {Branch : Type}
    (sameAffineClass : Branch → Branch → Prop) (I : Branch) (isBranch : Branch → Prop)
    (hI : isBranch I) (h_all : ∀ J, isBranch J → sameAffineClass I J) :
    ∃ Q, isBranch Q ∧ ∀ J, isBranch J → sameAffineClass Q J := by
  exact ⟨I, hI, h_all⟩

end Omega.Conclusion
