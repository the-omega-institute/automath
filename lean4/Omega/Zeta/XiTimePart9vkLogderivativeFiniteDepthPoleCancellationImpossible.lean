import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9vk-logderivative-finite-depth-pole-cancellation-impossible`. -/
theorem paper_xi_time_part9vk_logderivative_finite_depth_pole_cancellation_impossible
    (N : ℕ) (phi : ℂ) (hphi : phi ≠ 0) (c : ℕ → ℂ)
    (hres : ∀ r ≤ N, (∑ j ∈ Finset.range (r + 1), c j * phi ^ j) = 0) :
    ∀ j ≤ N, c j = 0 := by
  intro j
  refine Nat.strong_induction_on j ?_
  intro r ih hrN
  have hprev : (∑ k ∈ Finset.range r, c k * phi ^ k) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hkr : k < r := Finset.mem_range.mp hk
    have hkN : k ≤ N := Nat.le_trans (Nat.le_of_lt hkr) hrN
    simp [ih k hkr hkN]
  have hlast : c r * phi ^ r = 0 := by
    have h := hres r hrN
    rw [Finset.sum_range_succ, hprev, zero_add] at h
    exact h
  exact (mul_eq_zero.mp hlast).resolve_right (pow_ne_zero r hphi)

end Omega.Zeta
