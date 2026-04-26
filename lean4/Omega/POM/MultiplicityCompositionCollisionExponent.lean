import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionLogconvexLambdaq

namespace Omega.POM

noncomputable section

private lemma pom_multiplicity_composition_collision_exponent_lambda_sq (q : ℕ) :
    pomMultiplicityCompositionLambda q ^ (2 : Nat) =
      pomMomentHierarchyWeight q * pomMultiplicityCompositionLambda q + pomMomentHierarchyWeight q := by
  simpa [pomMultiplicityCompositionLambda] using
    (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.1 q).1

private lemma pom_multiplicity_composition_collision_exponent_weight_le_lambda (q : ℕ) :
    pomMomentHierarchyWeight q ≤ pomMultiplicityCompositionLambda q := by
  simpa [pomMultiplicityCompositionLambda] using
    (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.1 q).2.1

private lemma pom_multiplicity_composition_collision_exponent_lambda_pos (q : ℕ) :
    0 < pomMultiplicityCompositionLambda q := by
  simpa [pomMultiplicityCompositionLambda] using
    (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.1 q).2.2

private lemma pom_multiplicity_composition_collision_exponent_weight_pos (q : ℕ) :
    0 < pomMomentHierarchyWeight q := by
  unfold pomMomentHierarchyWeight
  positivity

private lemma pom_multiplicity_composition_collision_exponent_partition_pos (q : ℕ) :
    ∀ L : ℕ, 0 < pomMomentHierarchyPartition q L
  | 0 => by simp [pomMomentHierarchyPartition]
  | 1 => by
      simpa [pomMomentHierarchyPartition] using
        pom_multiplicity_composition_collision_exponent_weight_pos q
  | L + 2 => by
      have hnext :=
        pom_multiplicity_composition_collision_exponent_partition_pos q (L + 1)
      have hcurr := pom_multiplicity_composition_collision_exponent_partition_pos q L
      have hweight_pos := pom_multiplicity_composition_collision_exponent_weight_pos q
      simp [pomMomentHierarchyPartition, hweight_pos, hnext, hcurr, add_pos]

private lemma pom_multiplicity_composition_collision_exponent_partition_upper (q L : ℕ) :
    pomMomentHierarchyPartition q L ≤ pomMultiplicityCompositionLambda q ^ L := by
  simpa [pomMultiplicityCompositionLambda] using
    (paper_pom_multiplicity_composition_moment_hierarchy_rational_growth.2.2.2.2 q L)

private lemma pom_multiplicity_composition_collision_exponent_partition_lower (q : ℕ) :
    ∀ L : ℕ,
      (pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
          pomMultiplicityCompositionLambda q ^ L ≤
        pomMomentHierarchyPartition q L
  | 0 => by
      have hlam_pos := pom_multiplicity_composition_collision_exponent_lambda_pos q
      have hweight_le := pom_multiplicity_composition_collision_exponent_weight_le_lambda q
      have hdiv_le : pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q ≤ 1 := by
        rw [div_le_iff₀ hlam_pos]
        simpa using hweight_le
      simpa [pomMomentHierarchyPartition] using hdiv_le
  | 1 => by
      have hlam_ne : pomMultiplicityCompositionLambda q ≠ 0 := by
        exact ne_of_gt (pom_multiplicity_composition_collision_exponent_lambda_pos q)
      have hmain :
        (pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
            pomMultiplicityCompositionLambda q ^ 1 =
          pomMomentHierarchyWeight q := by
            field_simp [hlam_ne]
      have hmain_le :
          (pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
              pomMultiplicityCompositionLambda q ^ 1 ≤
            pomMomentHierarchyWeight q := by
        linarith
      simpa [pomMomentHierarchyPartition] using hmain_le
  | L + 2 => by
      have hnext := pom_multiplicity_composition_collision_exponent_partition_lower q (L + 1)
      have hcurr := pom_multiplicity_composition_collision_exponent_partition_lower q L
      have hweight_nonneg : 0 ≤ pomMomentHierarchyWeight q := by
        exact le_of_lt (pom_multiplicity_composition_collision_exponent_weight_pos q)
      calc
        (pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
            pomMultiplicityCompositionLambda q ^ (L + 2) =
          pomMomentHierarchyWeight q *
            ((pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
                pomMultiplicityCompositionLambda q ^ (L + 1) +
              (pomMomentHierarchyWeight q / pomMultiplicityCompositionLambda q) *
                pomMultiplicityCompositionLambda q ^ L) := by
              rw [pow_add, pom_multiplicity_composition_collision_exponent_lambda_sq q]
              ring
        _ ≤ pomMomentHierarchyWeight q *
            (pomMomentHierarchyPartition q (L + 1) + pomMomentHierarchyPartition q L) := by
              gcongr
        _ = pomMomentHierarchyPartition q (L + 2) := by
              simp [pomMomentHierarchyPartition]

private lemma pom_multiplicity_composition_collision_exponent_ratio_pow (L : ℕ) :
    (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^ L *
        (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) =
      pomMultiplicityCompositionLambda 2 ^ L := by
  have hlam1_ne : pomMultiplicityCompositionLambda 1 ≠ 0 := by
    exact ne_of_gt (pom_multiplicity_composition_collision_exponent_lambda_pos 1)
  calc
    (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^ L *
        (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) =
      (pomMultiplicityCompositionLambda 2 ^ L /
          ((pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^ L) *
        (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
          rw [div_pow]
    _ = (pomMultiplicityCompositionLambda 2 ^ L /
          (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat)) *
        (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
          rw [show ((pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^ L =
              (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) by
            rw [← pow_mul, ← pow_mul]
            simp [Nat.mul_comm]]
    _ = pomMultiplicityCompositionLambda 2 ^ L := by
          field_simp [hlam1_ne]

/-- Paper label: `cor:pom-multiplicity-composition-collision-exponent`. The recurrence bounds for
`Z_L^(q)` sandwich each partition function between positive multiples of `λ_q^L`; specializing to
`q = 1, 2` yields the matching exponential envelope for the collision ratio
`Z_L^(2) / (Z_L^(1))^2`. -/
theorem paper_pom_multiplicity_composition_collision_exponent :
    ∃ c_minus c_plus : ℝ,
      0 < c_minus ∧
        c_minus ≤ c_plus ∧
          ∃ N : ℕ,
            ∀ L ≥ N,
              c_minus *
                  (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                    (2 : Nat)) ^
                    L ≤
                pomMomentHierarchyPartition 2 L / (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) ∧
                pomMomentHierarchyPartition 2 L / (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) ≤
                  c_plus *
                    (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                      (2 : Nat)) ^
                      L := by
  let c1 : ℝ := pomMomentHierarchyWeight 1 / pomMultiplicityCompositionLambda 1
  let c2 : ℝ := pomMomentHierarchyWeight 2 / pomMultiplicityCompositionLambda 2
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    exact div_pos
      (pom_multiplicity_composition_collision_exponent_weight_pos 1)
      (pom_multiplicity_composition_collision_exponent_lambda_pos 1)
  have hc2_pos : 0 < c2 := by
    dsimp [c2]
    exact div_pos
      (pom_multiplicity_composition_collision_exponent_weight_pos 2)
      (pom_multiplicity_composition_collision_exponent_lambda_pos 2)
  refine ⟨c2, 1 / c1 ^ (2 : Nat), hc2_pos, ?_, 0, ?_⟩
  · have hc2_le_one : c2 ≤ 1 := by
      dsimp [c2]
      rw [div_le_iff₀ (pom_multiplicity_composition_collision_exponent_lambda_pos 2)]
      simpa using pom_multiplicity_composition_collision_exponent_weight_le_lambda 2
    have hc1_sq_pos : 0 < c1 ^ (2 : Nat) := by positivity
    have hc1_sq_le_one : c1 ^ (2 : Nat) ≤ 1 := by
      have hc1_le_one : c1 ≤ 1 := by
        dsimp [c1]
        rw [div_le_iff₀ (pom_multiplicity_composition_collision_exponent_lambda_pos 1)]
        simpa using pom_multiplicity_composition_collision_exponent_weight_le_lambda 1
      nlinarith [sq_nonneg c1]
    have hone_le : (1 : ℝ) ≤ 1 / c1 ^ (2 : Nat) := by
      rw [one_le_div hc1_sq_pos]
      exact hc1_sq_le_one
    exact le_trans hc2_le_one hone_le
  · intro L hL
    have hpart1_pos : 0 < pomMomentHierarchyPartition 1 L :=
      pom_multiplicity_composition_collision_exponent_partition_pos 1 L
    have hpart1_sq_pos : 0 < (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) := by positivity
    have hpart1_sq_upper :
        (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) ≤
          (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
      have hupper1 := pom_multiplicity_composition_collision_exponent_partition_upper 1 L
      have hpart1_nonneg : 0 ≤ pomMomentHierarchyPartition 1 L := le_of_lt hpart1_pos
      have hlam_nonneg : 0 ≤ pomMultiplicityCompositionLambda 1 ^ L := by
        exact pow_nonneg
          (le_of_lt (pom_multiplicity_composition_collision_exponent_lambda_pos 1)) L
      nlinarith [hupper1, sq_nonneg (pomMomentHierarchyPartition 1 L),
        sq_nonneg (pomMultiplicityCompositionLambda 1 ^ L)]
    have hpart1_sq_lower :
        (c1 * pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) ≤
          (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) := by
      have hlower1 := pom_multiplicity_composition_collision_exponent_partition_lower 1 L
      have hnonneg : 0 ≤ c1 * pomMultiplicityCompositionLambda 1 ^ L := by
        have hlam_nonneg : 0 ≤ pomMultiplicityCompositionLambda 1 ^ L := by
          exact pow_nonneg
            (le_of_lt (pom_multiplicity_composition_collision_exponent_lambda_pos 1)) L
        nlinarith [le_of_lt hc1_pos, hlam_nonneg]
      have hpart_nonneg : 0 ≤ pomMomentHierarchyPartition 1 L := le_of_lt hpart1_pos
      nlinarith [hlower1, sq_nonneg (c1 * pomMultiplicityCompositionLambda 1 ^ L),
        sq_nonneg (pomMomentHierarchyPartition 1 L)]
    constructor
    · rw [le_div_iff₀ hpart1_sq_pos]
      have hratio_nonneg :
          0 ≤ c2 *
            (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat)) ^
              L := by
        have hbase_pos :
            0 < pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat) := by
          exact div_pos
            (pom_multiplicity_composition_collision_exponent_lambda_pos 2)
            (pow_pos (pom_multiplicity_composition_collision_exponent_lambda_pos 1) _)
        have hpow_nonneg :
            0 ≤
              (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                (2 : Nat)) ^
                L := by
          exact le_of_lt (pow_pos hbase_pos L)
        nlinarith [le_of_lt hc2_pos, hpow_nonneg]
      calc
        c2 *
            (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat)) ^
              L *
            (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) ≤
          c2 *
            (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat)) ^
              L *
            (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
              nlinarith [hpart1_sq_upper, hratio_nonneg]
        _ = c2 * pomMultiplicityCompositionLambda 2 ^ L := by
              rw [mul_assoc, pom_multiplicity_composition_collision_exponent_ratio_pow]
        _ ≤ pomMomentHierarchyPartition 2 L := by
              exact pom_multiplicity_composition_collision_exponent_partition_lower 2 L
    · rw [div_le_iff₀ hpart1_sq_pos]
      have hratio_nonneg :
          0 ≤ (1 / c1 ^ (2 : Nat)) *
            (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat)) ^
              L := by
        have hbase_pos :
            0 < pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
              (2 : Nat) := by
          exact div_pos
            (pom_multiplicity_composition_collision_exponent_lambda_pos 2)
            (pow_pos (pom_multiplicity_composition_collision_exponent_lambda_pos 1) _)
        have hpow_nonneg :
            0 ≤
              (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                (2 : Nat)) ^
                L := by
          exact le_of_lt (pow_pos hbase_pos L)
        have hone_div_nonneg : 0 ≤ 1 / c1 ^ (2 : Nat) := by
          positivity
        nlinarith
      calc
        pomMomentHierarchyPartition 2 L ≤ pomMultiplicityCompositionLambda 2 ^ L := by
          exact pom_multiplicity_composition_collision_exponent_partition_upper 2 L
        _ = (1 / c1 ^ (2 : Nat)) *
              (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                (2 : Nat)) ^
                L *
              (c1 * pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
                have hc1_ne : c1 ≠ 0 := ne_of_gt hc1_pos
                have hmain :
                    (1 / c1 ^ (2 : Nat)) *
                        (pomMultiplicityCompositionLambda 2 /
                          (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^
                          L *
                        (c1 * pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) =
                      pomMultiplicityCompositionLambda 2 ^ L := by
                  have hcancel :
                      (1 / c1 ^ (2 : Nat)) *
                          (pomMultiplicityCompositionLambda 2 /
                            (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^
                            L *
                          (c1 * pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) =
                        (pomMultiplicityCompositionLambda 2 /
                            (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^
                            L *
                          (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := by
                    rw [pow_two, pow_two]
                    field_simp [hc1_ne]
                  calc
                    (1 / c1 ^ (2 : Nat)) *
                        (pomMultiplicityCompositionLambda 2 /
                          (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^
                          L *
                        (c1 * pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) =
                      (pomMultiplicityCompositionLambda 2 /
                          (pomMultiplicityCompositionLambda 1) ^ (2 : Nat)) ^
                          L *
                        (pomMultiplicityCompositionLambda 1 ^ L) ^ (2 : Nat) := hcancel
                    _ = pomMultiplicityCompositionLambda 2 ^ L := by
                          rw [pom_multiplicity_composition_collision_exponent_ratio_pow]
                exact hmain.symm
        _ ≤ (1 / c1 ^ (2 : Nat)) *
              (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                (2 : Nat)) ^
                L *
              (pomMomentHierarchyPartition 1 L) ^ (2 : Nat) := by
                nlinarith [hpart1_sq_lower, hratio_nonneg]

end

end Omega.POM
