import Omega.Discussion.ChebyshevAdams
import Omega.Discussion.UniqueContinuousTransversal

namespace Omega.Discussion

/-- Endpoint discussion package: the endpoint residue is discrete, while the only admissible
continuous transverse channel is the unique one packaged by the minimal-record-axis theorem.
    cor:discussion-endpoint-discrete-vs-continuous -/
theorem paper_discussion_endpoint_discrete_vs_continuous
    (m : Nat) (D : Omega.CircleDimension.MinimalRecordAxisData) :
    (Omega.Discussion.chebyAdams m 0 = 0 ∨ Omega.Discussion.chebyAdams m 0 = -2 ∨
        Omega.Discussion.chebyAdams m 0 = 2) ∧
      D.uniqueContinuousTransverse := by
  exact ⟨(paper_half_angle_z4_residue m).1, paper_discussion_unique_continuous_transversal D⟩

end Omega.Discussion
