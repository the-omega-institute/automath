import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingGeometricMixture

namespace Omega.POM

/-- The audited absorbing tail law obtained by summing the geometric masses from the hitting-time
mixture. -/
def pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail (k : ℕ) : ℚ :=
  diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k +
    diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k

/-- Forward difference on sequences. -/
def pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff (f : ℕ → ℚ) : ℕ → ℚ :=
  fun k => f (k + 1) - f k

/-- Iterated forward difference. -/
def pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff :
    ℕ → (ℕ → ℚ) → ℕ → ℚ
  | 0, f => f
  | m + 1, f =>
      pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
        (pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff f)

lemma pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul (c : ℚ) :
    ∀ m (f : ℕ → ℚ) (k : ℕ),
      pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
          (fun n => c * f n) k =
        c * pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m f k
  | 0, f, k => rfl
  | m + 1, f, k => by
      simpa [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff,
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff,
        mul_sub_left_distrib] using
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul c m
          (pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff f) k

lemma pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_add :
    ∀ m (f g : ℕ → ℚ) (k : ℕ),
      pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
          (fun n => f n + g n) k =
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m f k +
          pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m g k
  | 0, f, g, k => rfl
  | m + 1, f, g, k => by
      have hfd :
          pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff
              (fun n => f n + g n) =
            fun n =>
              pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff f n +
                pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff g n := by
        ext n
        simp [pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm]
      simpa [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff,
        hfd] using
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_add m
          (pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff f)
          (pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff g) k

lemma pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff_geometric (lam : ℚ) :
    pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff (fun n => lam ^ n) =
      fun k => (lam - 1) * lam ^ k := by
  ext k
  simp [pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff, pow_succ']
  ring

lemma pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_geometric (lam : ℚ) :
    ∀ m k,
      pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
          (fun n => lam ^ n) k =
        lam ^ k * (lam - 1) ^ m
  | 0, k => by simp [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff]
  | m + 1, k => by
      rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff,
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_forward_diff_geometric,
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul]
      rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_geometric]
      rw [pow_succ]
      ring

lemma pom_diagonal_rate_absorbing_hausdorff_moment_tail_signed_geometric (lam : ℚ) (m k : ℕ) :
    (-1 : ℚ) ^ m *
        pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
          (fun n => lam ^ n) k =
      lam ^ k * (1 - lam) ^ m := by
  rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_geometric]
  calc
    (-1 : ℚ) ^ m * (lam ^ k * (lam - 1) ^ m)
        = lam ^ k * ((-1 : ℚ) ^ m * (lam - 1) ^ m) := by ring
    _ = lam ^ k * (((-1 : ℚ) * (lam - 1)) ^ m) := by rw [← mul_pow]
    _ = lam ^ k * (1 - lam) ^ m := by
      congr 1
      ring

/-- Concrete statement of the tail formula and its complete monotonicity witness. -/
def pom_diagonal_rate_absorbing_hausdorff_moment_tail_statement : Prop :=
  (∀ k : ℕ,
      pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail k =
        diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k +
          diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k) ∧
    pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail 0 = 1 ∧
    (∀ m k : ℕ,
      (-1 : ℚ) ^ m *
          pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
            pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail k =
        diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k *
            (1 - diagonalRateAbsorbingGeometricLambda₁) ^ m +
          diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k *
            (1 - diagonalRateAbsorbingGeometricLambda₂) ^ m) ∧
    (∀ m k : ℕ,
      0 ≤
        (-1 : ℚ) ^ m *
          pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
            pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail k)

/-- Paper label: `cor:pom-diagonal-rate-absorbing-hausdorff-moment-tail`. -/
theorem paper_pom_diagonal_rate_absorbing_hausdorff_moment_tail :
    pom_diagonal_rate_absorbing_hausdorff_moment_tail_statement := by
  rcases paper_pom_diagonal_rate_absorbing_geometric_mixture with
    ⟨_, _, hWeight₁_pos, hWeight₂_pos, hWeight_sum, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    rfl
  · simpa [pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail] using hWeight_sum
  · intro m k
    unfold pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail
    rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_add]
    rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul]
    rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul]
    calc
      (-1 : ℚ) ^ m *
          (diagonalRateAbsorbingGeometricWeight₁ *
              pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                (fun n => diagonalRateAbsorbingGeometricLambda₁ ^ n) k +
            diagonalRateAbsorbingGeometricWeight₂ *
              pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                (fun n => diagonalRateAbsorbingGeometricLambda₂ ^ n) k)
          =
            diagonalRateAbsorbingGeometricWeight₁ *
                ((-1 : ℚ) ^ m *
                  pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                    (fun n => diagonalRateAbsorbingGeometricLambda₁ ^ n) k) +
              diagonalRateAbsorbingGeometricWeight₂ *
                ((-1 : ℚ) ^ m *
                  pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                    (fun n => diagonalRateAbsorbingGeometricLambda₂ ^ n) k) := by
              ring
      _ = diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k *
            (1 - diagonalRateAbsorbingGeometricLambda₁) ^ m +
          diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k *
            (1 - diagonalRateAbsorbingGeometricLambda₂) ^ m := by
            rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_signed_geometric]
            rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_signed_geometric]
            ring
  · intro m k
    have hFormula :
        (-1 : ℚ) ^ m *
            pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
              pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail k =
          diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k *
              (1 - diagonalRateAbsorbingGeometricLambda₁) ^ m +
            diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k *
              (1 - diagonalRateAbsorbingGeometricLambda₂) ^ m := by
      unfold pom_diagonal_rate_absorbing_hausdorff_moment_tail_tail
      rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_add]
      rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul]
      rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff_const_mul]
      calc
        (-1 : ℚ) ^ m *
            (diagonalRateAbsorbingGeometricWeight₁ *
                pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                  (fun n => diagonalRateAbsorbingGeometricLambda₁ ^ n) k +
              diagonalRateAbsorbingGeometricWeight₂ *
                pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                  (fun n => diagonalRateAbsorbingGeometricLambda₂ ^ n) k)
            =
              diagonalRateAbsorbingGeometricWeight₁ *
                  ((-1 : ℚ) ^ m *
                    pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                      (fun n => diagonalRateAbsorbingGeometricLambda₁ ^ n) k) +
                diagonalRateAbsorbingGeometricWeight₂ *
                  ((-1 : ℚ) ^ m *
                    pom_diagonal_rate_absorbing_hausdorff_moment_tail_iter_forward_diff m
                      (fun n => diagonalRateAbsorbingGeometricLambda₂ ^ n) k) := by
                ring
        _ = diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k *
              (1 - diagonalRateAbsorbingGeometricLambda₁) ^ m +
            diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k *
              (1 - diagonalRateAbsorbingGeometricLambda₂) ^ m := by
              rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_signed_geometric]
              rw [pom_diagonal_rate_absorbing_hausdorff_moment_tail_signed_geometric]
              ring
    rw [hFormula]
    have hWeight₁_nonneg : 0 ≤ diagonalRateAbsorbingGeometricWeight₁ := le_of_lt hWeight₁_pos
    have hWeight₂_nonneg : 0 ≤ diagonalRateAbsorbingGeometricWeight₂ := le_of_lt hWeight₂_pos
    have hLambda₁_nonneg : 0 ≤ diagonalRateAbsorbingGeometricLambda₁ := by
      norm_num [diagonalRateAbsorbingGeometricLambda₁, diagonalRateAbsorbingGeometricRoot₁]
    have hLambda₂_nonneg : 0 ≤ diagonalRateAbsorbingGeometricLambda₂ := by
      norm_num [diagonalRateAbsorbingGeometricLambda₂, diagonalRateAbsorbingGeometricRoot₂]
    have hOneMinusLambda₁_nonneg : 0 ≤ 1 - diagonalRateAbsorbingGeometricLambda₁ := by
      norm_num [diagonalRateAbsorbingGeometricLambda₁, diagonalRateAbsorbingGeometricRoot₁]
    have hOneMinusLambda₂_nonneg : 0 ≤ 1 - diagonalRateAbsorbingGeometricLambda₂ := by
      norm_num [diagonalRateAbsorbingGeometricLambda₂, diagonalRateAbsorbingGeometricRoot₂]
    have hTerm₁ :
        0 ≤ diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k *
          (1 - diagonalRateAbsorbingGeometricLambda₁) ^ m := by
      positivity
    have hTerm₂ :
        0 ≤ diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k *
          (1 - diagonalRateAbsorbingGeometricLambda₂) ^ m := by
      positivity
    linarith

end Omega.POM
