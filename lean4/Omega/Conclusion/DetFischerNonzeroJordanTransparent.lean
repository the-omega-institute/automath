import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper label: `thm:conclusion-det-fischer-nonzero-jordan-transparent`. The nilpotent
resolvent factor is the finite geometric inverse of `1 - z * N`. -/
theorem paper_conclusion_det_fischer_nonzero_jordan_transparent {R : Type*} [CommRing R]
    (N z : R) (m : Nat) (hN : N ^ m = 0) :
    (1 - z * N) * (∑ j ∈ Finset.range m, z ^ j * N ^ j) = 1 := by
  calc
    (1 - z * N) * (∑ j ∈ Finset.range m, z ^ j * N ^ j)
        = (1 - z * N) * (∑ j ∈ Finset.range m, (z * N) ^ j) := by
          congr 1
          exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]
    _ = 1 - (z * N) ^ m := by
      exact mul_neg_geom_sum (z * N) m
    _ = 1 := by
      rw [mul_pow, hN, mul_zero, sub_zero]

end Omega.Conclusion
