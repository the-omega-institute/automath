import Omega.Discussion.FoldRepresentationQCollisionLowerBound

namespace Omega.Discussion

/-- Paper-facing corollary: once the intrinsic `q`-collision exponential law is available,
the occupied-threshold consequence follows immediately from the previously established wrapper.
    cor:discussion-fold-intrinsic-qcollision-threshold -/
theorem paper_discussion_fold_intrinsic_qcollision_threshold
    (intrinsicQCollisionExpLaw occupancyThreshold : Prop)
    (hExpLaw : intrinsicQCollisionExpLaw)
    (hThreshold : intrinsicQCollisionExpLaw -> occupancyThreshold) :
    intrinsicQCollisionExpLaw ∧ occupancyThreshold := by
  exact ⟨hExpLaw, hThreshold hExpLaw⟩

end Omega.Discussion
