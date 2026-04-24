import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.GroupUnification

open scoped BigOperators

/-- In the `Q(√5)` specialization, once every valuation away from the rational prime `5`
vanishes, the residual discriminant stiffness is supported entirely at `5`.
    cor:gut-qsqrtfive-ramified-prime-stiffness -/
theorem paper_gut_qsqrtfive_ramified_prime_stiffness
    (s : Finset ℕ) (v : ℕ → ℤ) (detVal : ℤ)
    (hval : detVal = Finset.sum s v)
    (hunit : ∀ p ∈ s, p ≠ 5 → v p = 0)
    (hfive : 5 ∈ s) :
    Finset.sum (s.erase 5) v = 0 ∧ detVal = v 5 := by
  have hzero : Finset.sum (s.erase 5) v = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    exact hunit p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
  refine ⟨hzero, ?_⟩
  calc
    detVal = Finset.sum s v := hval
    _ = v 5 + Finset.sum (s.erase 5) v := by
      simpa [add_comm] using (Finset.sum_erase_add (s := s) (a := 5) (f := v) hfive).symm
    _ = v 5 := by rw [hzero, add_zero]

end Omega.GroupUnification
