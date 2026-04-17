import Omega.CircleDimension.MinimalRecordAxis

namespace Omega.Discussion

/-- Discussion-level wrapper around the minimal-record-axis package: the admissible continuous
transversal is unique.
    thm:discussion-unique-continuous-transversal -/
theorem paper_discussion_unique_continuous_transversal
    (D : Omega.CircleDimension.MinimalRecordAxisData) : D.uniqueContinuousTransverse := by
  exact (Omega.CircleDimension.paper_cdim_minimal_record_axis D).2.1

end Omega.Discussion
