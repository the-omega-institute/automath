import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete input package for the path hard-core pressure estimate. -/
structure conclusion_fiber_hardcore_partition_pressure_single_root_data where
  lengths : List ℕ
  activity : ℝ
  activity_nonneg : 0 ≤ activity

/-- The hard-core independent-set partition polynomial of a path of length `n`. -/
def conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition (t : ℝ) :
    ℕ → ℝ
  | 0 => 1
  | 1 => 1 + t
  | n + 2 =>
      conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) +
        t * conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n

/-- Multiplicative partition function over path components. -/
def conclusion_fiber_hardcore_partition_pressure_single_root_partition
    (D : conclusion_fiber_hardcore_partition_pressure_single_root_data) : ℝ :=
  (D.lengths.map
      (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition D.activity)).prod

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_recurrence
    (t : ℝ) (n : ℕ) :
    conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 2) =
      conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) +
        t * conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n := by
  rfl

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ n : ℕ, 0 ≤ conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n
  | 0 => by simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
  | 1 => by
      simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
      linarith
  | n + 2 => by
      change
        0 ≤
          conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) +
            t * conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n
      exact add_nonneg
        (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_nonneg ht (n + 1))
        (mul_nonneg ht
          (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_nonneg ht n))

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_pos
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ n : ℕ, 0 < conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n
  | 0 => by simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
  | 1 => by
      simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
      linarith
  | n + 2 => by
      simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
      have hprev :
          0 < conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) :=
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_pos ht (n + 1)
      have hnonneg :
          0 ≤ t *
            conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n := by
        exact mul_nonneg ht
          (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_nonneg ht n)
      linarith

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_bound
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ n : ℕ,
      conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n ≤ (1 + t) ^ n
  | 0 => by simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
  | 1 => by simp [conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition]
  | n + 2 => by
      have h₁ :
          conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) ≤
            (1 + t) ^ (n + 1) :=
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_bound ht (n + 1)
      have h₀ :
          conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n ≤
            (1 + t) ^ n :=
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_bound ht n
      have hpow_nonneg : 0 ≤ (1 + t) ^ n := by
        exact pow_nonneg (by linarith : 0 ≤ 1 + t) n
      have hterm :
          t * conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n ≤
            t * (1 + t) ^ n := by
        exact mul_le_mul_of_nonneg_left h₀ ht
      calc
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 2)
            =
              conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t (n + 1) +
                t * conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t n := by
              rfl
        _ ≤ (1 + t) ^ (n + 1) + t * (1 + t) ^ n := by linarith
        _ = (1 + t) ^ n * (1 + 2 * t) := by
              rw [show n + 1 = n + 1 by rfl, pow_succ]
              ring
        _ ≤ (1 + t) ^ n * (1 + t) ^ 2 := by
              have hquad : 1 + 2 * t ≤ (1 + t) ^ 2 := by nlinarith [sq_nonneg t]
              exact mul_le_mul_of_nonneg_left hquad hpow_nonneg
        _ = (1 + t) ^ (n + 2) := by
              rw [show n + 2 = n + 2 by rfl, pow_add]

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_partition_pos
    (D : conclusion_fiber_hardcore_partition_pressure_single_root_data) :
    0 < conclusion_fiber_hardcore_partition_pressure_single_root_partition D := by
  dsimp [conclusion_fiber_hardcore_partition_pressure_single_root_partition]
  exact List.prod_pos fun z hz => by
    rw [List.mem_map] at hz
    rcases hz with ⟨n, -, rfl⟩
    exact conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_pos
      D.activity_nonneg n

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_partition_bound_list
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ lengths : List ℕ,
      (lengths.map
        (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t)).prod ≤
        (1 + t) ^ lengths.sum
  | [] => by
      simp
  | ell :: rest => by
      have hhead :
          conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t ell ≤
            (1 + t) ^ ell :=
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_bound
          ht ell
      have htail_nonneg :
          0 ≤
            (rest.map
              (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition
                t)).prod := by
        exact List.prod_nonneg fun z hz => by
          rw [List.mem_map] at hz
          rcases hz with ⟨n, -, rfl⟩
          exact conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_nonneg
            ht n
      have hpow_nonneg : 0 ≤ (1 + t) ^ ell := by
        exact pow_nonneg (by linarith : 0 ≤ 1 + t) ell
      calc
        ((ell :: rest).map
            (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t)).prod
            =
              conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t ell *
                (rest.map
                  (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition t)).prod := by
              simp
        _ ≤ (1 + t) ^ ell * (1 + t) ^ rest.sum := by
              exact mul_le_mul hhead
                (conclusion_fiber_hardcore_partition_pressure_single_root_partition_bound_list
                  ht rest)
                htail_nonneg hpow_nonneg
        _ = (1 + t) ^ (ell :: rest).sum := by
              simp [pow_add]

private lemma conclusion_fiber_hardcore_partition_pressure_single_root_partition_bound
    (D : conclusion_fiber_hardcore_partition_pressure_single_root_data) :
    conclusion_fiber_hardcore_partition_pressure_single_root_partition D ≤
      (1 + D.activity) ^ D.lengths.sum := by
  simpa [conclusion_fiber_hardcore_partition_pressure_single_root_partition] using
    conclusion_fiber_hardcore_partition_pressure_single_root_partition_bound_list
      D.activity_nonneg D.lengths

/-- Concrete statement: recurrence, component product, and the logarithmic pressure bound. -/
def conclusion_fiber_hardcore_partition_pressure_single_root_statement
    (D : conclusion_fiber_hardcore_partition_pressure_single_root_data) : Prop :=
  (∀ n : ℕ,
      conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition D.activity (n + 2) =
        conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition D.activity (n + 1) +
          D.activity *
            conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition D.activity n) ∧
    conclusion_fiber_hardcore_partition_pressure_single_root_partition D =
      (D.lengths.map
        (conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition D.activity)).prod ∧
    Real.log (conclusion_fiber_hardcore_partition_pressure_single_root_partition D) ≤
      Real.log ((1 + D.activity) ^ D.lengths.sum)

/-- Paper label: `thm:conclusion-fiber-hardcore-partition-pressure-single-root`. -/
theorem paper_conclusion_fiber_hardcore_partition_pressure_single_root
    (D : conclusion_fiber_hardcore_partition_pressure_single_root_data) :
    conclusion_fiber_hardcore_partition_pressure_single_root_statement D := by
  refine ⟨?_, rfl, ?_⟩
  · exact conclusion_fiber_hardcore_partition_pressure_single_root_pathPartition_recurrence
      D.activity
  · exact Real.log_le_log
      (conclusion_fiber_hardcore_partition_pressure_single_root_partition_pos D)
      (conclusion_fiber_hardcore_partition_pressure_single_root_partition_bound D)

end

end Omega.Conclusion
