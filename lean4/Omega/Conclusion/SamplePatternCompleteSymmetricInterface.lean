import Omega.Conclusion.MixedCollisionOverlapMultisetRigidity
import Omega.POM.ClosurePartitionToFullRecoveryCurve
import Omega.POM.FiniteParetoLegendreCurvature
import Omega.POM.OracleSuccessExponentTwoMeasureCompetition

namespace Omega.Conclusion

/-- Concrete two-sample interface used to expose the overlap multiset. -/
def conclusion_sample_pattern_complete_symmetric_interface_w0 : Bool → Rat
  | false => 2
  | true => 1

/-- Second concrete sample used for the same overlap package. -/
def conclusion_sample_pattern_complete_symmetric_interface_w1 : Bool → Rat
  | false => 1
  | true => 3

/-- Symmetric two-weight Pareto model used for the escort boundary package. -/
def conclusion_sample_pattern_complete_symmetric_interface_paretoData :
    Omega.POM.PomFiniteParetoLegendreData where
  leftWeight := 1
  rightWeight := 1
  leftWeight_pos := by norm_num
  rightWeight_pos := by norm_num

/-- Paper label: `thm:conclusion-sample-pattern-complete-symmetric-interface`. The recovered
overlap multiset, the partition-to-full-recovery curve package, the explicit two-weight Pareto
boundary, and the quadratic oracle-success competition fit together into one concrete symmetric
interface. -/
theorem paper_conclusion_sample_pattern_complete_symmetric_interface :
    mixedCollisionOverlapMultisetRigidity
        conclusion_sample_pattern_complete_symmetric_interface_w0
        conclusion_sample_pattern_complete_symmetric_interface_w1 ∧
    Omega.POM.pom_closure_partition_to_full_recovery_curve_statement ∧
    Omega.POM.PomFiniteParetoLegendreData.strictLegendreGeometry
        conclusion_sample_pattern_complete_symmetric_interface_paretoData ∧
    (let qStar :=
        Omega.POM.pom_oracle_success_exponent_two_measure_competition_criticalOrder 1 0 1
      let E := Omega.POM.pom_oracle_success_exponent_two_measure_competition_failureBranch 1 0 0 1
      let U := Omega.POM.pom_oracle_success_exponent_two_measure_competition_uniformBranch 1 0 0 1
      let S :=
        Omega.POM.pom_oracle_success_exponent_two_measure_competition_successExponent
          1 0 0 1 0 0 1
      S = min E U ∧
        (∃! q : ℝ, 1 < q ∧
          Omega.POM.pom_oracle_success_exponent_two_measure_competition_failureObjective
            1 0 0 1 q = E) ∧
        Omega.POM.pom_oracle_success_exponent_two_measure_competition_failurePrime 1 0 1 =
          (qStar - 1) * Real.log 2 ∧
        Omega.POM.pom_oracle_success_exponent_two_measure_competition_failureSecond 1 =
          (Real.log 2) ^ 2 ∧
        0 < Omega.POM.pom_oracle_success_exponent_two_measure_competition_failureSecond 1 ∧
        0 <
          Omega.POM.pom_oracle_success_exponent_two_measure_competition_criticalOrder 1 0 1 - 1 ∧
        0 < Omega.POM.pom_oracle_success_exponent_two_measure_competition_failureSecond 1 ∧
        (E ≤ U → S = E) ∧
        (U ≤ E → S = U)) := by
  refine ⟨?_, Omega.POM.paper_pom_closure_partition_to_full_recovery_curve, ?_, ?_⟩
  · exact paper_conclusion_mixed_collision_overlap_multiset_rigidity
      conclusion_sample_pattern_complete_symmetric_interface_w0
      conclusion_sample_pattern_complete_symmetric_interface_w1
  · exact Omega.POM.paper_pom_finite_pareto_legendre_curvature
      conclusion_sample_pattern_complete_symmetric_interface_paretoData
  · simpa using
      Omega.POM.paper_pom_oracle_success_exponent_two_measure_competition
        1 0 0 1 0 0 1 (by norm_num) (by norm_num) (by simpa using Real.log_pos one_lt_two)

end Omega.Conclusion
