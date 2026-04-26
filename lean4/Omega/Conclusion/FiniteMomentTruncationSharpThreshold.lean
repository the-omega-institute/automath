import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete data for the sharpness threshold of truncated moment recovery. -/
structure conclusion_finite_moment_truncation_sharp_threshold_data where
  M_m : ℕ
  M_m_pos : 1 ≤ M_m

/-- The first `M_m` support points are encoded as `t + 1` for `t ∈ range M_m`. -/
def conclusion_finite_moment_truncation_sharp_threshold_moment
    (D : conclusion_finite_moment_truncation_sharp_threshold_data) (h : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range D.M_m, h t * (((t + 1 : ℕ) ^ n : ℕ) : ℤ)

/-- The alternating binomial perturbation supported on `{1, ..., M}`. -/
def conclusion_finite_moment_truncation_sharp_threshold_kernel (M t : ℕ) : ℤ :=
  (-1 : ℤ) ^ (M - (t + 1)) * (M.choose (t + 1) : ℤ)

namespace conclusion_finite_moment_truncation_sharp_threshold_data

/-- The first `M_m - 1` moments do not determine the histogram uniquely, but the `M_m`-th moment
separates the explicit binomial perturbation from the constant histogram. -/
def sharp_threshold (D : conclusion_finite_moment_truncation_sharp_threshold_data) : Prop :=
  ∃ hPlus hMinus : ℕ → ℤ,
    (∀ t, t < D.M_m → 0 < hPlus t) ∧
      (∀ t, t < D.M_m → 0 < hMinus t) ∧
      (∃ t, t < D.M_m ∧ hPlus t ≠ hMinus t) ∧
      (∀ n, 1 ≤ n → n ≤ D.M_m - 1 →
        conclusion_finite_moment_truncation_sharp_threshold_moment D hPlus n =
          conclusion_finite_moment_truncation_sharp_threshold_moment D hMinus n) ∧
      conclusion_finite_moment_truncation_sharp_threshold_moment D hPlus D.M_m ≠
        conclusion_finite_moment_truncation_sharp_threshold_moment D hMinus D.M_m

end conclusion_finite_moment_truncation_sharp_threshold_data

private theorem conclusion_finite_moment_truncation_sharp_threshold_kernel_sum_eq_zero
    {M n : ℕ} (hn1 : 1 ≤ n) (hnM : n < M) :
    ∑ t ∈ Finset.range M,
      conclusion_finite_moment_truncation_sharp_threshold_kernel M t *
        (((t + 1 : ℕ) ^ n : ℕ) : ℤ) = 0 := by
  have hzero_fun := (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) hnM)
  have hzero := congrArg (fun f : ℤ → ℤ => f 0) hzero_fun
  have hzero' :
      ∑ x ∈ Finset.range M,
          (-1 : ℤ) ^ (M - (x + 1)) * (M.choose (x + 1) : ℤ) * ((x + 1 : ℤ) ^ n) +
        (-1 : ℤ) ^ M * (0 : ℤ) ^ n = 0 := by
    simpa [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ',
      conclusion_finite_moment_truncation_sharp_threshold_kernel] using hzero
  have hzeroTerm : (-1 : ℤ) ^ M * (0 : ℤ) ^ n = 0 := by
    have hn0 : n ≠ 0 := by omega
    simp [hn0]
  rw [hzeroTerm, add_zero] at hzero'
  simpa [conclusion_finite_moment_truncation_sharp_threshold_kernel] using hzero'

private theorem conclusion_finite_moment_truncation_sharp_threshold_kernel_sum_eq_factorial
    {M : ℕ} (hM : 1 ≤ M) :
    ∑ t ∈ Finset.range M,
      conclusion_finite_moment_truncation_sharp_threshold_kernel M t *
        (((t + 1 : ℕ) ^ M : ℕ) : ℤ) = (Nat.factorial M : ℤ) := by
  have hfac := congrArg (fun f : ℤ → ℤ => f 0) (fwdDiff_iter_eq_factorial (R := ℤ) (n := M))
  have hfac' :
      ∑ x ∈ Finset.range M,
          (-1 : ℤ) ^ (M - (x + 1)) * (M.choose (x + 1) : ℤ) * ((x + 1 : ℤ) ^ M) +
        (-1 : ℤ) ^ M * (0 : ℤ) ^ M = (Nat.factorial M : ℤ) := by
    simpa [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ',
      conclusion_finite_moment_truncation_sharp_threshold_kernel] using hfac
  have hzeroTerm : (-1 : ℤ) ^ M * (0 : ℤ) ^ M = 0 := by
    have hM0 : M ≠ 0 := by omega
    simp [hM0]
  rw [hzeroTerm, add_zero] at hfac'
  simpa [conclusion_finite_moment_truncation_sharp_threshold_kernel] using hfac'

private theorem conclusion_finite_moment_truncation_sharp_threshold_kernel_abs_bound
    (M t : ℕ) :
    |conclusion_finite_moment_truncation_sharp_threshold_kernel M t| ≤ (2 ^ M : ℤ) := by
  rw [conclusion_finite_moment_truncation_sharp_threshold_kernel]
  have habs :
      |(-1 : ℤ) ^ (M - (t + 1)) * (M.choose (t + 1) : ℤ)| = (M.choose (t + 1) : ℤ) := by
    simp
  rw [habs]
  exact_mod_cast Nat.choose_le_two_pow M (t + 1)

/-- Paper label: `thm:conclusion-finite-moment-truncation-sharp-threshold`. -/
theorem paper_conclusion_finite_moment_truncation_sharp_threshold
    (D : conclusion_finite_moment_truncation_sharp_threshold_data) : D.sharp_threshold := by
  let L : ℤ := (2 ^ D.M_m : ℤ) + 1
  let hMinus : ℕ → ℤ := fun _ => L
  let hPlus : ℕ → ℤ := fun t =>
    L + conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t
  refine ⟨hPlus, hMinus, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hbound :=
      conclusion_finite_moment_truncation_sharp_threshold_kernel_abs_bound D.M_m t
    have hlower : -((2 ^ D.M_m : ℤ)) ≤
        conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t := by
      calc
        -((2 ^ D.M_m : ℤ)) ≤
            -|conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t| := by
              exact neg_le_neg hbound
        _ ≤ conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t := neg_abs_le _
    have hL : 0 < L := by
      dsimp [L]
      positivity
    dsimp [hPlus]
    linarith
  · intro t ht
    dsimp [hMinus, L]
    positivity
  · have hlt : D.M_m - 1 < D.M_m := by
      exact Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one D.M_m_pos) (by decide)
    refine ⟨D.M_m - 1, hlt, ?_⟩
    have hlast : D.M_m - 1 + 1 = D.M_m := by
      omega
    dsimp [hPlus, hMinus]
    simp [L, conclusion_finite_moment_truncation_sharp_threshold_kernel, hlast]
  · intro n hn1 hn
    have hnM : n < D.M_m := by
      omega
    unfold conclusion_finite_moment_truncation_sharp_threshold_moment
    calc
      ∑ t ∈ Finset.range D.M_m,
          hPlus t * (((t + 1 : ℕ) ^ n : ℕ) : ℤ)
        = ∑ t ∈ Finset.range D.M_m,
            (L * (((t + 1 : ℕ) ^ n : ℕ) : ℤ) +
              conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t *
                (((t + 1 : ℕ) ^ n : ℕ) : ℤ)) := by
            apply Finset.sum_congr rfl
            intro t ht
            dsimp [hPlus]
            ring
      _ = (∑ t ∈ Finset.range D.M_m, L * (((t + 1 : ℕ) ^ n : ℕ) : ℤ)) +
            ∑ t ∈ Finset.range D.M_m,
              conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t *
                (((t + 1 : ℕ) ^ n : ℕ) : ℤ) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ t ∈ Finset.range D.M_m, hMinus t * (((t + 1 : ℕ) ^ n : ℕ) : ℤ) := by
            rw [conclusion_finite_moment_truncation_sharp_threshold_kernel_sum_eq_zero hn1 hnM]
            simp [hMinus]
  · have hfac :
        ∑ t ∈ Finset.range D.M_m,
          conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t *
            (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ) = (Nat.factorial D.M_m : ℤ) :=
      conclusion_finite_moment_truncation_sharp_threshold_kernel_sum_eq_factorial D.M_m_pos
    have hsplit :
        conclusion_finite_moment_truncation_sharp_threshold_moment D hPlus D.M_m =
          conclusion_finite_moment_truncation_sharp_threshold_moment D hMinus D.M_m +
            (Nat.factorial D.M_m : ℤ) := by
      unfold conclusion_finite_moment_truncation_sharp_threshold_moment
      calc
        ∑ t ∈ Finset.range D.M_m,
            hPlus t * (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ)
          = ∑ t ∈ Finset.range D.M_m,
              (L * (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ) +
                conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t *
                  (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ)) := by
              apply Finset.sum_congr rfl
              intro t ht
              dsimp [hPlus]
              ring
        _ = (∑ t ∈ Finset.range D.M_m, L * (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ)) +
              ∑ t ∈ Finset.range D.M_m,
                conclusion_finite_moment_truncation_sharp_threshold_kernel D.M_m t *
                  (((t + 1 : ℕ) ^ D.M_m : ℕ) : ℤ) := by
              rw [Finset.sum_add_distrib]
        _ = conclusion_finite_moment_truncation_sharp_threshold_moment D hMinus D.M_m +
              (Nat.factorial D.M_m : ℤ) := by
              rw [hfac]
              simp [hMinus, conclusion_finite_moment_truncation_sharp_threshold_moment]
    intro heq
    rw [heq] at hsplit
    have hfac_pos : 0 < (Nat.factorial D.M_m : ℤ) := by
      exact_mod_cast Nat.factorial_pos D.M_m
    linarith

end Omega.Conclusion
