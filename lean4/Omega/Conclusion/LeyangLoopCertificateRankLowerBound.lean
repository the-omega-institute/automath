import Mathlib.Tactic

namespace Omega.Conclusion

/-- Corrected loop-certificate data for
`thm:conclusion-leyang-loop-certificate-rank-lower-bound`.  The key hypothesis is explicit:
the certificate rank dominates the first homology rank of the punctured sphere loop space. -/
structure conclusion_leyang_loop_certificate_rank_lower_bound_data where
  branchValueCount : ℕ
  homologyRank : ℕ
  certificateRank : ℕ
  conclusion_leyang_loop_certificate_rank_lower_bound_homologyRank_eq_pred :
    homologyRank = branchValueCount - 1
  conclusion_leyang_loop_certificate_rank_lower_bound_certificate_dominates_homology :
    homologyRank ≤ certificateRank
  conclusion_leyang_loop_certificate_rank_lower_bound_leyang_branchValueCount :
    branchValueCount = 6

namespace conclusion_leyang_loop_certificate_rank_lower_bound_data

/-- The Lee--Yang specialization of the loop-certificate lower bound. -/
def leyangRankBound (D : conclusion_leyang_loop_certificate_rank_lower_bound_data) : Prop :=
  5 ≤ D.certificateRank

end conclusion_leyang_loop_certificate_rank_lower_bound_data

open conclusion_leyang_loop_certificate_rank_lower_bound_data

/-- Paper label: `thm:conclusion-leyang-loop-certificate-rank-lower-bound`. -/
theorem paper_conclusion_leyang_loop_certificate_rank_lower_bound
    (D : conclusion_leyang_loop_certificate_rank_lower_bound_data) :
    D.homologyRank ≤ D.certificateRank ∧ D.leyangRankBound := by
  constructor
  · exact D.conclusion_leyang_loop_certificate_rank_lower_bound_certificate_dominates_homology
  · have hhom : D.homologyRank = 5 := by
      calc
        D.homologyRank = D.branchValueCount - 1 :=
          D.conclusion_leyang_loop_certificate_rank_lower_bound_homologyRank_eq_pred
        _ = 6 - 1 := by
          rw [D.conclusion_leyang_loop_certificate_rank_lower_bound_leyang_branchValueCount]
        _ = 5 := by norm_num
    simpa [leyangRankBound, hhom] using
      D.conclusion_leyang_loop_certificate_rank_lower_bound_certificate_dominates_homology

end Omega.Conclusion
