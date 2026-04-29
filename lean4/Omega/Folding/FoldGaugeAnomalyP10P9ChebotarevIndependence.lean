import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10P9LinearDisjointness

namespace Omega.Folding

/-- The audited `P10/P9` arithmetic package used for the Chebotarev factorization. -/
def fold_gauge_anomaly_p10_p9_chebotarev_independence_data : FoldGaugeAnomalyP10P9Data where
  p10QuadraticSubfield := 66269989
  p9QuadraticSubfield := 33605193
  p10SplittingDegree := Nat.factorial 10
  p9SplittingDegree := Nat.factorial 9
  p10QuadraticSubfield_eq := rfl
  p9QuadraticSubfield_eq := rfl
  p10SplittingDegree_eq := rfl
  p9SplittingDegree_eq := rfl

/-- Density of the `10`-cycle class inside the audited `S₁₀` factor. -/
def fold_gauge_anomaly_p10_p9_chebotarev_independence_p10_ten_cycle_density : ℚ :=
  (Nat.factorial 9 : ℚ) / Fintype.card (Equiv.Perm (Fin 10))

/-- Density of the identity class inside the audited `S₉` factor. -/
def fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density : ℚ :=
  (1 : ℚ) / Fintype.card (Equiv.Perm (Fin 9))

/-- Product density coming from the direct-product Chebotarev factorization. -/
def fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density : ℚ :=
  fold_gauge_anomaly_p10_p9_chebotarev_independence_p10_ten_cycle_density *
    fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density

/-- Paper label: `cor:fold-gauge-anomaly-P10-P9-chebotarev-independence`. -/
theorem paper_fold_gauge_anomaly_p10_p9_chebotarev_independence :
    fold_gauge_anomaly_p10_p9_chebotarev_independence_data.galoisGroupIsDirectProduct ∧
      fold_gauge_anomaly_p10_p9_chebotarev_independence_p10_ten_cycle_density = (1 : ℚ) / 10 ∧
      fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density =
        (1 : ℚ) / Nat.factorial 9 ∧
      fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density =
        ((1 : ℚ) / 10) * ((1 : ℚ) / Nat.factorial 9) ∧
      fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density =
        (1 : ℚ) / (10 * Nat.factorial 9) := by
  have hdirect :
      fold_gauge_anomaly_p10_p9_chebotarev_independence_data.galoisGroupIsDirectProduct := by
    exact
      (paper_fold_gauge_anomaly_P10_P9_linear_disjointness
        fold_gauge_anomaly_p10_p9_chebotarev_independence_data).2.1
  have hp10 :
      fold_gauge_anomaly_p10_p9_chebotarev_independence_p10_ten_cycle_density = (1 : ℚ) / 10 := by
    unfold fold_gauge_anomaly_p10_p9_chebotarev_independence_p10_ten_cycle_density
    rw [Fintype.card_perm]
    norm_num [Nat.factorial]
  have hp9 :
      fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density =
        (1 : ℚ) / Nat.factorial 9 := by
    unfold fold_gauge_anomaly_p10_p9_chebotarev_independence_p9_identity_density
    rw [Fintype.card_perm, Fintype.card_fin]
  refine ⟨hdirect, hp10, hp9, ?_, ?_⟩
  · unfold fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density
    rw [hp10, hp9]
  · calc
      fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density =
          ((1 : ℚ) / 10) * ((1 : ℚ) / Nat.factorial 9) := by
            unfold fold_gauge_anomaly_p10_p9_chebotarev_independence_joint_density
            rw [hp10, hp9]
      _ = (1 : ℚ) / (10 * Nat.factorial 9) := by
            norm_num [Nat.factorial]

end Omega.Folding
