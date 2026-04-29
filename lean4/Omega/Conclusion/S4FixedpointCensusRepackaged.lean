import Omega.Conclusion.S4HodgeDeterminesFixedpointCounts

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-s4-fixedpoint-census-repackaged`. -/
theorem paper_conclusion_s4_fixedpoint_census_repackaged :
    let fix := conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz
    fix .transposition = 24 ∧
      fix .doubleTransposition = 0 ∧
        fix .threeCycle = 0 ∧
          fix .fourCycle = 0 := by
  norm_num [conclusion_s4_hodge_determines_fixedpoint_counts_holomorphic_lefschetz,
    conclusion_s4_hodge_determines_fixedpoint_counts_hodge_character,
    conclusion_s4_hodge_determines_fixedpoint_counts_sgn_character,
    conclusion_s4_hodge_determines_fixedpoint_counts_v2_character,
    conclusion_s4_hodge_determines_fixedpoint_counts_v3_character,
    conclusion_s4_hodge_determines_fixedpoint_counts_v3prime_character]

end Omega.Conclusion
