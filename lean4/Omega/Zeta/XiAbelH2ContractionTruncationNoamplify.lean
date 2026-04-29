import Mathlib.Tactic

namespace Omega.Zeta

private theorem xi_abel_h2_contraction_truncation_noamplify_selected_square_sum_le
    (b : ℕ → ℝ) (k M : ℕ) (hk : 0 < k) :
    (Finset.range M).sum (fun m => (b (k * m)) ^ 2) ≤
      (Finset.range (k * M)).sum (fun n => (b n) ^ 2) := by
  let S := (Finset.range M).image fun m => k * m
  have hS_subset : S ⊆ Finset.range (k * M) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    exact Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hm) hk)
  have hsum_image :
      (Finset.range M).sum (fun m => (b (k * m)) ^ 2) =
        S.sum (fun n => (b n) ^ 2) := by
    dsimp [S]
    rw [Finset.sum_image]
    intro m _ n _ hmn
    exact Nat.eq_of_mul_eq_mul_left hk hmn
  calc
    (Finset.range M).sum (fun m => (b (k * m)) ^ 2) =
        S.sum (fun n => (b n) ^ 2) := hsum_image
    _ ≤ (Finset.range (k * M)).sum (fun n => (b n) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_subset (fun n _ _ => sq_nonneg (b n))

/-- Paper label: `prop:xi-abel-H2-contraction-truncation-noamplify`. -/
theorem paper_xi_abel_h2_contraction_truncation_noamplify
    (a : ℕ → ℝ) (k N : ℕ) (hk : 2 ≤ k) :
    (∀ M, (Finset.range M).sum (fun m => (a (k * m)) ^ 2) ≤
        (Finset.range (k * M)).sum (fun n => (a n) ^ 2)) ∧
      (∀ M, (Finset.range M).sum
          (fun m => (a (k * m) - if k * m ≤ N then a (k * m) else 0) ^ 2) ≤
        (Finset.range (k * M)).sum
          (fun n => (a n - if n ≤ N then a n else 0) ^ 2)) := by
  have hk_pos : 0 < k := by omega
  constructor
  · intro M
    exact xi_abel_h2_contraction_truncation_noamplify_selected_square_sum_le a k M hk_pos
  · intro M
    exact xi_abel_h2_contraction_truncation_noamplify_selected_square_sum_le
      (fun n => a n - if n ≤ N then a n else 0) k M hk_pos

end Omega.Zeta
