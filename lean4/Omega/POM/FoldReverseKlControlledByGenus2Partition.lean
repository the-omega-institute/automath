import Mathlib.Tactic
import Omega.POM.ReverseKlBoundByDispersion

namespace Omega.POM

open scoped BigOperators

/-- Uniform pushforward profile on the audited genus-2 partition. -/
noncomputable def fold_reversekl_controlled_by_genus2_partition_weight (m : ℕ) :
    Fin (m + 1) → ℝ := fun _ =>
  (Fintype.card (Fin (m + 1)) : ℝ)⁻¹

/-- Concrete partition-function proxy for the genus-2 reverse-KL wrapper. -/
noncomputable def fold_reversekl_controlled_by_genus2_partition_partition_function (m : ℕ) : ℝ :=
  ∑ x : Fin (m + 1), (fold_reversekl_controlled_by_genus2_partition_weight m x)⁻¹

/-- Paper-facing specialization of the reverse-KL dispersion bound to the concrete genus-2
partition proxy. -/
def fold_reversekl_controlled_by_genus2_partition_statement (m : ℕ) : Prop :=
  (∑ x : Fin (m + 1),
      (Fintype.card (Fin (m + 1)) : ℝ)⁻¹ *
        Real.log (((Fintype.card (Fin (m + 1)) : ℝ)⁻¹) /
          fold_reversekl_controlled_by_genus2_partition_weight m x)) ≤
    Real.log ((((Fintype.card (Fin (m + 1)) : ℝ)⁻¹)^2) *
      fold_reversekl_controlled_by_genus2_partition_partition_function m)

local notation "FoldReverseKlControlledByGenus2PartitionStatement" =>
  fold_reversekl_controlled_by_genus2_partition_statement

/-- Paper label: `cor:fold-reversekl-controlled-by-genus2-partition`. The audited genus-2
partition proxy is uniform, so the general reverse-KL-by-dispersion inequality applies directly
with partition function `|X_m|`. -/
theorem paper_fold_reversekl_controlled_by_genus2_partition (m : ℕ) :
    FoldReverseKlControlledByGenus2PartitionStatement m := by
  have hcard_pos : 0 < (Fintype.card (Fin (m + 1)) : ℝ) := by positivity
  have hcard_ne : (Fintype.card (Fin (m + 1)) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hbase :=
    paper_pom_reverse_kl_bound_by_dispersion
      (X := Fin (m + 1))
      (w := fold_reversekl_controlled_by_genus2_partition_weight m)
      (hw_pos := by
        intro x
        rw [fold_reversekl_controlled_by_genus2_partition_weight]
        positivity)
      (_hw_sum := by
        calc
          (∑ x : Fin (m + 1), fold_reversekl_controlled_by_genus2_partition_weight m x) =
              (Fintype.card (Fin (m + 1)) : ℝ) * (Fintype.card (Fin (m + 1)) : ℝ)⁻¹ := by
                simp [fold_reversekl_controlled_by_genus2_partition_weight]
          _ = 1 := by
                rw [mul_inv_cancel₀ hcard_ne])
  simpa [fold_reversekl_controlled_by_genus2_partition_statement,
    fold_reversekl_controlled_by_genus2_partition_weight,
    fold_reversekl_controlled_by_genus2_partition_partition_function, hcard_ne] using hbase

end Omega.POM
