import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

theorem paper_xi_time_part60ab_gauge_constant_richardson_neville_accelerator
    {R m : ℕ} (γ lam a : ℕ → ℝ) (L : ℝ)
    (hγ : (∑ j ∈ Finset.range (R + 1), γ j) = 1)
    (hzero : ∀ r ∈ Finset.Icc 1 R,
      (∑ j ∈ Finset.range (R + 1), γ j * (lam r) ^ j) = 0) :
    (∑ j ∈ Finset.range (R + 1),
      γ j * (L + ∑ r ∈ Finset.Icc 1 R, a r * (lam r) ^ (m + j))) = L := by
  have hconst : (∑ j ∈ Finset.range (R + 1), γ j * L) = L := by
    rw [← Finset.sum_mul, hγ]
    ring
  have hmodal :
      (∑ j ∈ Finset.range (R + 1),
        γ j * (∑ r ∈ Finset.Icc 1 R, a r * (lam r) ^ (m + j))) =
        ∑ r ∈ Finset.Icc 1 R,
          (a r * (lam r) ^ m) * (∑ j ∈ Finset.range (R + 1), γ j * (lam r) ^ j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring
  have hmodal_zero :
      (∑ r ∈ Finset.Icc 1 R,
        (a r * (lam r) ^ m) * (∑ j ∈ Finset.range (R + 1), γ j * (lam r) ^ j)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [hzero r hr, mul_zero]
  calc
    (∑ j ∈ Finset.range (R + 1),
      γ j * (L + ∑ r ∈ Finset.Icc 1 R, a r * (lam r) ^ (m + j)))
        = (∑ j ∈ Finset.range (R + 1), γ j * L) +
          (∑ j ∈ Finset.range (R + 1),
            γ j * (∑ r ∈ Finset.Icc 1 R, a r * (lam r) ^ (m + j))) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
    _ = L := by
      rw [hconst, hmodal, hmodal_zero, add_zero]

end Omega.Zeta
