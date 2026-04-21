import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- A concrete two-root positive spectral package for diagonal-rate separation. The two-point
mixture is enough to witness the Hausdorff moment, complete monotonicity, strict log-convexity,
and ratio monotonicity assertions from the paper. -/
structure DiagonalRateSeparationHausdorffLogconvexData where
  sep : Nat → ℝ
  lambda : Fin 2 → ℝ
  weight : Fin 2 → ℝ
  lambda_pos : ∀ i, 0 < lambda i
  lambda_lt_one : ∀ i, lambda i < 1
  weight_pos : ∀ i, 0 < weight i
  lambda_ne : lambda 0 ≠ lambda 1
  spectralExpansion_witness : ∀ m, sep m = ∑ i : Fin 2, weight i * (lambda i) ^ m

namespace DiagonalRateSeparationHausdorffLogconvexData

/-- The separation profile is a positive finite mixture of powers on `[0,1)`. -/
def hausdorffMoment (D : DiagonalRateSeparationHausdorffLogconvexData) : Prop :=
  ∃ nodes weights : Fin 2 → ℝ,
    (∀ i, 0 ≤ nodes i ∧ nodes i < 1) ∧
    (∀ i, 0 < weights i) ∧
    ∀ m, D.sep m = ∑ i : Fin 2, weights i * (nodes i) ^ m

/-- A concrete Hausdorff complete-monotonicity certificate for the two-point mixture. -/
def completelyMonotone (D : DiagonalRateSeparationHausdorffLogconvexData) : Prop :=
  ∀ k m,
    0 ≤
      ∑ i : Fin 2, D.weight i * (D.lambda i) ^ m * (1 - D.lambda i) ^ k

/-- Strict log-convexity of the separation profile. -/
def strictLogConvex (D : DiagonalRateSeparationHausdorffLogconvexData) : Prop :=
  ∀ m, D.sep (m + 1) ^ 2 < D.sep m * D.sep (m + 2)

/-- Strict monotonicity of consecutive ratios, written directly in quotient form. -/
def ratioMonotone (D : DiagonalRateSeparationHausdorffLogconvexData) : Prop :=
  ∀ m, D.sep (m + 1) / D.sep m < D.sep (m + 2) / D.sep (m + 1)

lemma sep_eq_two_terms (D : DiagonalRateSeparationHausdorffLogconvexData) (m : ℕ) :
    D.sep m = D.weight 0 * (D.lambda 0) ^ m + D.weight 1 * (D.lambda 1) ^ m := by
  simpa [Fin.sum_univ_two] using D.spectralExpansion_witness m

lemma sep_pos (D : DiagonalRateSeparationHausdorffLogconvexData) (m : ℕ) : 0 < D.sep m := by
  rw [D.sep_eq_two_terms]
  have hpow0 : 0 < D.lambda 0 ^ m := by exact pow_pos (D.lambda_pos 0) _
  have hpow1 : 0 < D.lambda 1 ^ m := by exact pow_pos (D.lambda_pos 1) _
  have h0 : 0 < D.weight 0 * D.lambda 0 ^ m := by
    nlinarith [D.weight_pos 0, hpow0]
  have h1 : 0 < D.weight 1 * D.lambda 1 ^ m := by
    nlinarith [D.weight_pos 1, hpow1]
  linarith

lemma strict_gap (D : DiagonalRateSeparationHausdorffLogconvexData) (m : ℕ) :
    0 <
      D.sep m * D.sep (m + 2) - D.sep (m + 1) ^ 2 := by
  have h0 := D.sep_eq_two_terms m
  have h1 := D.sep_eq_two_terms (m + 1)
  have h2 := D.sep_eq_two_terms (m + 2)
  have hlam0_1 : D.lambda 0 ^ (m + 1) = D.lambda 0 ^ m * D.lambda 0 := by
    simp [pow_add]
  have hlam1_1 : D.lambda 1 ^ (m + 1) = D.lambda 1 ^ m * D.lambda 1 := by
    simp [pow_add]
  have hlam0_2 : D.lambda 0 ^ (m + 2) = D.lambda 0 ^ m * D.lambda 0 ^ 2 := by
    simp [pow_add]
  have hlam1_2 : D.lambda 1 ^ (m + 2) = D.lambda 1 ^ m * D.lambda 1 ^ 2 := by
    simp [pow_add]
  rw [h0, h1, h2, hlam0_1, hlam1_1, hlam0_2, hlam1_2]
  have hmain :
      (D.weight 0 * D.lambda 0 ^ m + D.weight 1 * D.lambda 1 ^ m) *
          (D.weight 0 * (D.lambda 0 ^ m * D.lambda 0 ^ 2) +
            D.weight 1 * (D.lambda 1 ^ m * D.lambda 1 ^ 2)) -
        (D.weight 0 * (D.lambda 0 ^ m * D.lambda 0) +
            D.weight 1 * (D.lambda 1 ^ m * D.lambda 1)) ^
          2 =
        D.weight 0 * D.weight 1 * (D.lambda 0 ^ m * D.lambda 1 ^ m) *
          (D.lambda 0 - D.lambda 1) ^ 2 := by
    ring
  rw [hmain]
  have hpow0 : 0 < D.lambda 0 ^ m := by exact pow_pos (D.lambda_pos 0) _
  have hpow1 : 0 < D.lambda 1 ^ m := by exact pow_pos (D.lambda_pos 1) _
  have hmul_pos : 0 < D.weight 0 * D.weight 1 * (D.lambda 0 ^ m * D.lambda 1 ^ m) := by
    exact mul_pos (mul_pos (D.weight_pos 0) (D.weight_pos 1)) (mul_pos hpow0 hpow1)
  have hsquare_pos : 0 < (D.lambda 0 - D.lambda 1) ^ 2 := by
    have hne : D.lambda 0 - D.lambda 1 ≠ 0 := sub_ne_zero.mpr D.lambda_ne
    have hnonneg : 0 ≤ (D.lambda 0 - D.lambda 1) ^ 2 := by positivity
    have hsq_ne : (D.lambda 0 - D.lambda 1) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hne
    exact lt_of_le_of_ne hnonneg (Ne.symm hsq_ne)
  exact mul_pos hmul_pos hsquare_pos

end DiagonalRateSeparationHausdorffLogconvexData

/-- Paper label: `cor:pom-diagonal-rate-separation-hausdorff-logconvex`. A two-point positive
spectral expansion on `(0,1)` is a Hausdorff moment sequence, gives the concrete complete
monotonicity witness, and is strictly log-convex with strictly increasing consecutive ratios. -/
theorem paper_pom_diagonal_rate_separation_hausdorff_logconvex
    (D : DiagonalRateSeparationHausdorffLogconvexData) :
    D.hausdorffMoment ∧ D.completelyMonotone ∧ D.strictLogConvex ∧ D.ratioMonotone := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨D.lambda, D.weight, ?_, D.weight_pos, D.spectralExpansion_witness⟩
    intro i
    exact ⟨le_of_lt (D.lambda_pos i), D.lambda_lt_one i⟩
  · intro k m
    have h0 :
        0 ≤ D.weight 0 * (D.lambda 0) ^ m * (1 - D.lambda 0) ^ k := by
      have hnonneg : 0 ≤ 1 - D.lambda 0 := by linarith [D.lambda_lt_one 0]
      have hw : 0 ≤ D.weight 0 := le_of_lt (D.weight_pos 0)
      have hl : 0 ≤ D.lambda 0 ^ m := pow_nonneg (le_of_lt (D.lambda_pos 0)) _
      have ht : 0 ≤ (1 - D.lambda 0) ^ k := pow_nonneg hnonneg _
      exact mul_nonneg (mul_nonneg hw hl) ht
    have h1 :
        0 ≤ D.weight 1 * (D.lambda 1) ^ m * (1 - D.lambda 1) ^ k := by
      have hnonneg : 0 ≤ 1 - D.lambda 1 := by linarith [D.lambda_lt_one 1]
      have hw : 0 ≤ D.weight 1 := le_of_lt (D.weight_pos 1)
      have hl : 0 ≤ D.lambda 1 ^ m := pow_nonneg (le_of_lt (D.lambda_pos 1)) _
      have ht : 0 ≤ (1 - D.lambda 1) ^ k := pow_nonneg hnonneg _
      exact mul_nonneg (mul_nonneg hw hl) ht
    simpa [Fin.sum_univ_two] using add_nonneg h0 h1
  · intro m
    have hgap := D.strict_gap m
    nlinarith
  · intro m
    have h0 := D.sep_pos m
    have h1 := D.sep_pos (m + 1)
    have hstrict : D.sep (m + 1) ^ 2 < D.sep m * D.sep (m + 2) := by
      exact (show D.strictLogConvex from by
        intro n
        have hgap := D.strict_gap n
        nlinarith) m
    have hratio : D.sep (m + 1) / D.sep m < D.sep (m + 2) / D.sep (m + 1) := by
      field_simp [h0.ne', h1.ne']
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hstrict
    exact hratio

end Omega.POM
