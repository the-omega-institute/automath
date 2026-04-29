import Omega.Conclusion.DyadicBoundaryGodelAdmissibleMultiplicativeLinearSubcode
import Omega.Conclusion.DyadicBoundaryPathConsistencyQueryRankEqualsCheckRank

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-dyadic-boundary-godel-code-parameters-and-check-rank`. The
admissible dyadic boundary Gödel subcode has the full `2^(2^(mn))` cardinality, and the edge/check
rank quantities are already packaged in closed form. -/
theorem paper_conclusion_dyadic_boundary_godel_code_parameters_and_check_rank (m n : Nat) :
    Fintype.card (dyadicBoundaryAdmissibleSubcode m n) = 2 ^ (2 ^ (m * n)) ∧
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n =
        n * (2 ^ m + 1) * 2 ^ (m * (n - 1)) ∧
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n =
        (n - 1) * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) := by
  exact
    ⟨(paper_conclusion_dyadic_boundary_godel_admissible_multiplicative_linear_subcode m n).2.2.2,
      rfl, rfl⟩

end Omega.Conclusion
