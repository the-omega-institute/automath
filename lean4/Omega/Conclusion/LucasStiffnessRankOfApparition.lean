import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-lucas-stiffness-rank-of-apparition`. -/
theorem paper_conclusion_lucas_stiffness_rank_of_apparition
    (F : ℕ → ℤ) (v : ℤ → ℤ) (stiff : ℕ → ℤ) (ρ : ℕ) (hρ : 1 ≤ ρ)
    (hstiff : ∀ q,
      stiff q = 2 * (∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * v (F d)))
    (hzero : ∀ d, 1 ≤ d → d < ρ → v (F d) = 0) (hnonzero : v (F ρ) ≠ 0) :
    (∀ q, q < ρ → stiff q = 0) ∧
      stiff ρ - 2 * stiff (ρ - 1) + stiff (ρ - 2) ≠ 0 := by
  have hvanish : ∀ q, q < ρ → stiff q = 0 := by
    intro q hq
    rw [hstiff q]
    have hsum :
        (∑ d ∈ Finset.Icc 1 q, ((q + 1 - d : ℕ) : ℤ) * v (F d)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro d hd
      have hdmem := Finset.mem_Icc.mp hd
      have hv : v (F d) = 0 := hzero d hdmem.1 (lt_of_le_of_lt hdmem.2 hq)
      rw [hv, mul_zero]
    rw [hsum, mul_zero]
  constructor
  · exact hvanish
  · have hstiff_rho : stiff ρ = 2 * v (F ρ) := by
      rw [hstiff ρ]
      have hsum :
          (∑ d ∈ Finset.Icc 1 ρ, ((ρ + 1 - d : ℕ) : ℤ) * v (F d)) = v (F ρ) := by
        rw [Finset.sum_eq_single ρ]
        · have hcoeff : (ρ + 1 - ρ : ℕ) = 1 := by
            exact Nat.add_sub_cancel_left ρ 1
          rw [hcoeff]
          norm_num
        · intro d hd hdne
          have hdmem := Finset.mem_Icc.mp hd
          have hlt : d < ρ := lt_of_le_of_ne hdmem.2 hdne
          have hv : v (F d) = 0 := hzero d hdmem.1 hlt
          rw [hv, mul_zero]
        · intro hnotmem
          exact False.elim (hnotmem (Finset.mem_Icc.mpr ⟨hρ, le_rfl⟩))
      rw [hsum]
    have hpred : stiff (ρ - 1) = 0 := by
      exact hvanish (ρ - 1)
        (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hρ) Nat.zero_lt_one)
    have hpred2 : stiff (ρ - 2) = 0 := by
      exact hvanish (ρ - 2)
        (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hρ) (by decide : 0 < 2))
    rw [hstiff_rho, hpred, hpred2]
    norm_num
    exact hnonzero

end Omega.Conclusion
