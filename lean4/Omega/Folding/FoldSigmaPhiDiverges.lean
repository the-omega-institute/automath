import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Folding

/-- Paper label: `thm:fold-sigma-phi-diverges`. -/
theorem paper_fold_sigma_phi_diverges (Cphi : ℕ → ℝ) (c : ℝ) (n0 : ℕ) (hc : 0 < c)
    (hFib : ∀ n ≥ n0, c ≤ Cphi (Nat.fib n)) :
    ∀ B : ℝ, ∃ N : ℕ, B ≤ 1 + 2 * Finset.sum (Finset.range (N + 1)) (fun u => (Cphi u)^2) := by
  intro B
  by_cases hB : B ≤ 1
  · refine ⟨0, ?_⟩
    have hsum_nonneg : 0 ≤ Finset.sum (Finset.range (0 + 1)) (fun u => (Cphi u)^2) := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith
  · have hc_sq_pos : 0 < c ^ 2 := by nlinarith
    obtain ⟨k, hk⟩ := exists_nat_gt ((B - 1) / (2 * c ^ 2))
    let n1 : ℕ := max n0 2
    let N : ℕ := Nat.fib (n1 + k)
    let S : Finset ℕ := (Finset.range (k + 1)).image (fun i => Nat.fib (n1 + i))
    have hn1_ge_n0 : n0 ≤ n1 := by
      simp [n1]
    have hn1_ge_two : 2 ≤ n1 := by
      simp [n1]
    have hstrict : StrictMono fun i : ℕ => Nat.fib (n1 + i) := by
      refine strictMono_nat_of_lt_succ ?_
      intro i
      exact fib_strict_mono (n1 + i) (by omega)
    have hS_subset : S ⊆ Finset.range (N + 1) := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
      rw [Finset.mem_range]
      have hi' : i < k + 1 := Finset.mem_range.mp hi
      have hmono : Nat.fib (n1 + i) ≤ Nat.fib (n1 + k) := Nat.fib_mono (by omega)
      exact lt_of_le_of_lt hmono (Nat.lt_succ_self _)
    have hsum_subset :
        Finset.sum S (fun u => (Cphi u)^2)
          ≤ Finset.sum (Finset.range (N + 1)) (fun u => (Cphi u)^2) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hS_subset (fun _ _ _ => sq_nonneg _)
    have hsum_image :
        Finset.sum (Finset.range (k + 1)) (fun i => (Cphi (Nat.fib (n1 + i)))^2)
          = Finset.sum S (fun u => (Cphi u)^2) := by
      dsimp [S]
      rw [Finset.sum_image]
      intro i _ j _ hij
      exact hstrict.injective (by simpa using hij)
    have hterm :
        ∀ i ∈ Finset.range (k + 1), c ^ 2 ≤ (Cphi (Nat.fib (n1 + i))) ^ 2 := by
      intro i hi
      have hi_n0 : n0 ≤ n1 + i := by omega
      have hci : c ≤ Cphi (Nat.fib (n1 + i)) := hFib (n1 + i) hi_n0
      nlinarith
    have hsum_lower :
        ((k + 1 : ℕ) : ℝ) * c ^ 2
          ≤ Finset.sum (Finset.range (k + 1)) (fun i => (Cphi (Nat.fib (n1 + i)))^2) := by
      have hsum_const := Finset.sum_le_sum hterm
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum_const
    have hk_real : (B - 1) / (2 * c ^ 2) < (k : ℝ) := by
      exact_mod_cast hk
    have hk_succ : (B - 1) / (2 * c ^ 2) < ((k + 1 : ℕ) : ℝ) := by
      exact lt_of_lt_of_le hk_real (by exact_mod_cast (Nat.le_succ k))
    have hden_pos : 0 < 2 * c ^ 2 := by
      nlinarith
    have hB_count : B ≤ 1 + 2 * (((k + 1 : ℕ) : ℝ) * c ^ 2) := by
      have hmul :
          ((B - 1) / (2 * c ^ 2)) * (2 * c ^ 2) < ((k + 1 : ℕ) : ℝ) * (2 * c ^ 2) :=
        mul_lt_mul_of_pos_right hk_succ hden_pos
      have hcancel : ((B - 1) / (2 * c ^ 2)) * (2 * c ^ 2) = B - 1 := by
        field_simp [ne_of_gt hden_pos]
      rw [hcancel] at hmul
      nlinarith
    refine ⟨N, ?_⟩
    calc
      B ≤ 1 + 2 * (((k + 1 : ℕ) : ℝ) * c ^ 2) := hB_count
      _ ≤ 1 + 2 * Finset.sum (Finset.range (k + 1)) (fun i => (Cphi (Nat.fib (n1 + i)))^2) := by
        nlinarith
      _ = 1 + 2 * Finset.sum S (fun u => (Cphi u)^2) := by rw [hsum_image]
      _ ≤ 1 + 2 * Finset.sum (Finset.range (N + 1)) (fun u => (Cphi u)^2) := by
        nlinarith

end Omega.Folding
