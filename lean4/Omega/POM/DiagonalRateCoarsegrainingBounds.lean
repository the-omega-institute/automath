import Mathlib.Tactic
import Omega.POM.BlockConsistencyRateBlockReduction

namespace Omega.POM

open scoped BigOperators

section

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B] [Nonempty B]

/-- The blockwise collision mass of the normalized conditional law inside `b`. -/
noncomputable def pom_diagonal_rate_coarsegraining_bounds_blockCollisionMass
    (π : X → B) (w : X → ℝ) (b : B) : ℝ :=
  ∑ x : X, (normalizedBlockWeight π w b x) ^ 2

/-- The coarse-graining collision floor `c_π` from the paper. -/
noncomputable def pom_diagonal_rate_coarsegraining_bounds_cPi
    (π : X → B) (w : X → ℝ) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty
    (pom_diagonal_rate_coarsegraining_bounds_blockCollisionMass π w)

/-- The shifted diagonal-agreement budget induced by the collision floor. -/
noncomputable def pom_diagonal_rate_coarsegraining_bounds_deltaPrime (δ cπ : ℝ) : ℝ :=
  1 - (1 - δ) / cπ

omit [DecidableEq X] in
private lemma pom_diagonal_rate_coarsegraining_bounds_cPi_le
    (π : X → B) (w : X → ℝ) (b : B) :
    pom_diagonal_rate_coarsegraining_bounds_cPi π w ≤
      pom_diagonal_rate_coarsegraining_bounds_blockCollisionMass π w b := by
  classical
  unfold pom_diagonal_rate_coarsegraining_bounds_cPi
  exact Finset.inf'_le _ (by simp)

private lemma pom_diagonal_rate_coarsegraining_bounds_deltaPrime_le
    {δ cπ : ℝ} (hδ : δ ≤ 1) (hcπ_pos : 0 < cπ) (hcπ_le_one : cπ ≤ 1) :
    pom_diagonal_rate_coarsegraining_bounds_deltaPrime δ cπ ≤ δ := by
  have hδ_nonneg : 0 ≤ 1 - δ := by linarith
  have hcinv_ge_one : 1 ≤ 1 / cπ := by
    have hmul := (mul_le_mul_of_nonneg_left hcπ_le_one (show 0 ≤ 1 / cπ by positivity))
    simpa [hcπ_pos.ne', one_div, inv_mul_cancel₀, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdiv :
      1 - δ ≤ (1 - δ) / cπ := by
    have hmul :=
      mul_le_mul_of_nonneg_left hcinv_ge_one hδ_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  unfold pom_diagonal_rate_coarsegraining_bounds_deltaPrime
  linarith

/-- Paper label: `thm:pom-diagonal-rate-coarsegraining-bounds`. The chapter-local diagonal rate
is bounded below by its block coarse-graining via the existing block-reduction theorem, while the
collision floor `c_π` yields the upper bound at the shifted budget `δ' = 1 - (1 - δ) / c_π`. -/
theorem paper_pom_diagonal_rate_coarsegraining_bounds
    (π : X → B) (w : X → ℝ) (δ : ℝ)
    (hcπ_pos : 0 < pom_diagonal_rate_coarsegraining_bounds_cPi π w)
    (hcπ_le_one : pom_diagonal_rate_coarsegraining_bounds_cPi π w ≤ 1)
    (hδ : δ ≤ 1) :
    diagonalConsistencyRate (blockWeight π w) δ ≤ blockConsistencyRate π w δ ∧
      blockConsistencyRate π w δ ≤
        diagonalConsistencyRate (blockWeight π w)
          (pom_diagonal_rate_coarsegraining_bounds_deltaPrime δ
            (pom_diagonal_rate_coarsegraining_bounds_cPi π w)) ∧
      ∀ b : B,
        pom_diagonal_rate_coarsegraining_bounds_cPi π w ≤
          pom_diagonal_rate_coarsegraining_bounds_blockCollisionMass π w b := by
  let cπ := pom_diagonal_rate_coarsegraining_bounds_cPi π w
  have hEq :
      blockConsistencyRate π w δ = diagonalConsistencyRate (blockWeight π w) δ :=
    (paper_pom_block_consistency_rate_block_reduction (π := π) (w := w) (δ := δ)).1
  have hdelta :
      pom_diagonal_rate_coarsegraining_bounds_deltaPrime δ cπ ≤ δ :=
    pom_diagonal_rate_coarsegraining_bounds_deltaPrime_le hδ
      (by simp [cπ] at hcπ_pos ⊢; exact hcπ_pos) (by simpa [cπ] using hcπ_le_one)
  refine ⟨by simp [hEq], ?_, ?_⟩
  · rw [hEq]
    unfold diagonalConsistencyRate pom_diagonal_rate_coarsegraining_bounds_deltaPrime
    exact sub_le_sub_left hdelta _
  · intro b
    simpa [cπ] using pom_diagonal_rate_coarsegraining_bounds_cPi_le (π := π) (w := w) b

end

end Omega.POM
