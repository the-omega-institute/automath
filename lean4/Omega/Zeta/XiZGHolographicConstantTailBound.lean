import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite tail of the ZG holographic constant correction series.  The lower cutoff is written as
`N + 1` so the sum is exactly over the finite window `N < k ≤ M`. -/
noncomputable def xi_zg_holographic_constant_tail_bound_tail
    (Delta : ℕ → ℝ) (N M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (N + 1) M, Delta k

/-- Finite majorant for the same ZG holographic tail window.  In applications `majorant k` is the
prime-zeta expression `p_k^{-2} + (p_k p_{k-1})^{-1}`. -/
noncomputable def xi_zg_holographic_constant_tail_bound_majorant
    (majorant : ℕ → ℝ) (N M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (N + 1) M, majorant k

/-- Paper label: `prop:xi-zg-holographic-constant-tail-bound`.

The uniform pointwise estimate for the correction terms at `s = 1` sums over every finite tail
window.  Passing `M → ∞` in a summable application gives the stated infinite-tail estimate. -/
theorem paper_xi_zg_holographic_constant_tail_bound
    (Delta majorant : ℕ → ℝ) (C : ℝ) (N M : ℕ)
    (hpoint : ∀ k, N < k → |Delta k| ≤ C * majorant k) :
    |xi_zg_holographic_constant_tail_bound_tail Delta N M| ≤
      C * xi_zg_holographic_constant_tail_bound_majorant majorant N M := by
  unfold xi_zg_holographic_constant_tail_bound_tail
    xi_zg_holographic_constant_tail_bound_majorant
  calc
    |∑ k ∈ Finset.Icc (N + 1) M, Delta k| ≤
        ∑ k ∈ Finset.Icc (N + 1) M, |Delta k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc (N + 1) M, C * majorant k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk_lower : N < k := by
            have hk_mem := (Finset.mem_Icc.mp hk).1
            omega
          exact hpoint k hk_lower
    _ = C * ∑ k ∈ Finset.Icc (N + 1) M, majorant k := by
          rw [Finset.mul_sum]

end Omega.Zeta
