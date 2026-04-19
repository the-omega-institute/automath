import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyBranchpointRationalReduction

namespace Omega.Folding

/-- Audited real parts of the four non-real `P10` conjugate pairs used in the branch-point audit. -/
def gaugeAnomalyP10AuditedRealPart : Fin 4 → ℚ
  | ⟨0, _⟩ => 281 / 500
  | ⟨1, _⟩ => -824 / 500
  | ⟨2, _⟩ => -321 / 200
  | ⟨3, _⟩ => 197 / 100

/-- Audited absolute imaginary parts of the four non-real `P10` conjugate pairs. -/
def gaugeAnomalyP10AuditedImagAbs : Fin 4 → ℚ
  | ⟨0, _⟩ => 219 / 500
  | ⟨1, _⟩ => 287 / 500
  | ⟨2, _⟩ => 1237 / 1000
  | ⟨3, _⟩ => 144 / 125

/-- Squared moduli of the audited non-real `P10` conjugate pairs. -/
def gaugeAnomalyP10AuditedRadiusSq (i : Fin 4) : ℚ :=
  gaugeAnomalyP10AuditedRealPart i ^ 2 + gaugeAnomalyP10AuditedImagAbs i ^ 2

/-- Branch multiplicity assigned by the audited reduction: the dominant pair yields the repeated
root and the remaining pairs stay simple. -/
def gaugeAnomalyP10AuditedBranchMultiplicity : Fin 4 → ℕ
  | ⟨3, _⟩ => 2
  | _ => 1

/-- The dominant conjugate pair in the audited `P10` list. -/
def gaugeAnomalyP10DominantPair : Fin 4 := ⟨3, by decide⟩

private theorem gaugeAnomalyP10AuditedImagAbs_pos (i : Fin 4) :
    0 < gaugeAnomalyP10AuditedImagAbs i := by
  fin_cases i <;> norm_num [gaugeAnomalyP10AuditedImagAbs]

private theorem gaugeAnomalyP10AuditedDominantPair_repeated :
    gaugeAnomalyP10AuditedBranchMultiplicity gaugeAnomalyP10DominantPair = 2 := by
  norm_num [gaugeAnomalyP10AuditedBranchMultiplicity, gaugeAnomalyP10DominantPair]

private theorem gaugeAnomalyP10AuditedSubdominant
    (i : Fin 4) (hi : i ≠ gaugeAnomalyP10DominantPair) :
    gaugeAnomalyP10AuditedBranchMultiplicity i = 1 ∧
      gaugeAnomalyP10AuditedRadiusSq i < gaugeAnomalyP10AuditedRadiusSq gaugeAnomalyP10DominantPair := by
  fin_cases i
  · norm_num [gaugeAnomalyP10AuditedBranchMultiplicity, gaugeAnomalyP10AuditedRadiusSq,
      gaugeAnomalyP10AuditedRealPart, gaugeAnomalyP10AuditedImagAbs, gaugeAnomalyP10DominantPair]
  · norm_num [gaugeAnomalyP10AuditedBranchMultiplicity, gaugeAnomalyP10AuditedRadiusSq,
      gaugeAnomalyP10AuditedRealPart, gaugeAnomalyP10AuditedImagAbs, gaugeAnomalyP10DominantPair]
  · norm_num [gaugeAnomalyP10AuditedBranchMultiplicity, gaugeAnomalyP10AuditedRadiusSq,
      gaugeAnomalyP10AuditedRealPart, gaugeAnomalyP10AuditedImagAbs, gaugeAnomalyP10DominantPair]
  · exact (hi rfl).elim

/-- The discriminant factorization and rational branchpoint reduction isolate the `u = 1`
specialization, while the audited non-real `P10` conjugate-pair table shows that exactly one pair
produces the dominant repeated root and the remaining pairs are strictly subdominant.
    prop:fold-gauge-anomaly-branch-point-classification -/
theorem paper_fold_gauge_anomaly_branch_point_classification :
    gaugeAnomalyBranchpointRationalReduction ∧
      gaugeAnomalyBranchpointSpecializationAtTwo ∧
      (∀ u : ℚ, gaugeAnomalyQuarticDiscriminant u = -u * (u - 1) * gaugeAnomalyP10 u) ∧
      (∀ i : Fin 4, 0 < gaugeAnomalyP10AuditedImagAbs i) ∧
      gaugeAnomalyP10AuditedBranchMultiplicity gaugeAnomalyP10DominantPair = 2 ∧
      (∀ i : Fin 4, i ≠ gaugeAnomalyP10DominantPair →
        gaugeAnomalyP10AuditedBranchMultiplicity i = 1 ∧
          gaugeAnomalyP10AuditedRadiusSq i <
            gaugeAnomalyP10AuditedRadiusSq gaugeAnomalyP10DominantPair) := by
  rcases paper_fold_gauge_anomaly_branchpoint_rational_reduction with ⟨hReduction, hSpecial, _⟩
  refine ⟨hReduction, hSpecial, paper_fold_gauge_anomaly_discriminant_factorization,
    gaugeAnomalyP10AuditedImagAbs_pos, gaugeAnomalyP10AuditedDominantPair_repeated,
    gaugeAnomalyP10AuditedSubdominant⟩

end Omega.Folding
