import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

noncomputable section

/-- Paper label: `prop:gm-trace3-truncated-moment-rank2`. Splitting off a maximal
eigenvalue and averaging the remaining nonnegative entries gives the two-point Jensen lower
envelope for the third trace moment. -/
theorem paper_gm_trace3_truncated_moment_rank2 {m : ℕ} (hm : 2 ≤ m) (lambda : Fin m → ℝ)
    (i0 : Fin m) (hmax : ∀ i, lambda i ≤ lambda i0) (h_nonneg : ∀ i, 0 ≤ lambda i) :
    let x := lambda i0
    let y := ((∑ i, lambda i) - x) / ((m : ℝ) - 1)
    x ^ 3 + ((m : ℝ) - 1) * y ^ 3 ≤ ∑ i, (lambda i) ^ 3 := by
  dsimp
  have _ : lambda i0 ≤ lambda i0 := hmax i0
  let s : Finset (Fin m) := Finset.univ.erase i0
  have hm1_nat_pos : 0 < m - 1 := by omega
  have hm1_real_pos : 0 < (((m - 1 : ℕ) : ℝ)) := by exact_mod_cast hm1_nat_pos
  have hm_sub_real : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
  have hcard_s : s.card = m - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i0)]
    simp
  have hsum_tail_add :
      (∑ i ∈ s, lambda i) + lambda i0 = ∑ i, lambda i := by
    dsimp [s]
    simp
  have hsum_tail : (∑ i, lambda i) - lambda i0 = ∑ i ∈ s, lambda i := by
    rw [← hsum_tail_add]
    ring
  have hcube_tail_add :
      (∑ i ∈ s, (lambda i) ^ 3) + (lambda i0) ^ 3 = ∑ i, (lambda i) ^ 3 := by
    dsimp [s]
    simp
  have hjensen :=
    pow_sum_div_card_le_sum_pow (s := s) (f := lambda)
      (hf := by
        intro i _hi
        exact h_nonneg i)
      (n := 2)
  have htail_jensen :
      (∑ i ∈ s, lambda i) ^ 3 / (((m - 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ s, (lambda i) ^ 3 := by
    simpa [hcard_s, hm1_nat_pos] using hjensen
  have htail_rewrite :
      ((m : ℝ) - 1) * (((∑ i, lambda i) - lambda i0) / ((m : ℝ) - 1)) ^ 3 =
        (∑ i ∈ s, lambda i) ^ 3 / (((m - 1 : ℕ) : ℝ) ^ 2) := by
    rw [hsum_tail, hm_sub_real]
    field_simp [ne_of_gt hm1_real_pos]
  calc
    (lambda i0) ^ 3 +
        ((m : ℝ) - 1) * (((∑ i, lambda i) - lambda i0) / ((m : ℝ) - 1)) ^ 3
        ≤ (lambda i0) ^ 3 + ∑ i ∈ s, (lambda i) ^ 3 := by
          rw [htail_rewrite]
          exact add_le_add (le_refl _) htail_jensen
    _ = ∑ i, (lambda i) ^ 3 := by
          rw [add_comm]
          exact hcube_tail_add

end

end Omega.SyncKernelRealInput
