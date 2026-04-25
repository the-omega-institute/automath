import Omega.EA.FoldTailTopologicalReadout
import Omega.Folding.MomentSum

namespace Omega.EA

open scoped BigOperators

/-- Paper label: `prop:fold-large-fiber-moment-upperbounds`.
Large-fiber counts and large-fiber mass are controlled by the `q`-th fiber-multiplicity moment by
restricting `momentSum` to the fibers with multiplicity at least `D`. -/
theorem paper_fold_large_fiber_moment_upperbounds (m D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    Omega.EA.foldTailMultiplicity m D * D ^ q ≤ Omega.momentSum q m ∧
      (∑ x : Omega.X m, if D ≤ Omega.X.fiberMultiplicity x then Omega.X.fiberMultiplicity x else 0) *
          D ^ (q - 1) ≤
        Omega.momentSum q m := by
  let _ := hD
  constructor
  · rw [Omega.EA.foldTailMultiplicity, Nat.mul_comm, Finset.mul_sum, Omega.momentSum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : D ≤ Omega.X.fiberMultiplicity x
    · simp [hx]
      exact Nat.pow_le_pow_left hx q
    · simp [hx]
  · rw [Finset.sum_mul, Omega.momentSum]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : D ≤ Omega.X.fiberMultiplicity x
    · simp [hx]
      calc
        Omega.X.fiberMultiplicity x * D ^ (q - 1) ≤
            Omega.X.fiberMultiplicity x * Omega.X.fiberMultiplicity x ^ (q - 1) := by
              exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx _)
        _ = Omega.X.fiberMultiplicity x ^ ((q - 1) + 1) := by
              rw [Nat.mul_comm, ← Nat.pow_succ]
        _ = Omega.X.fiberMultiplicity x ^ q := by
              rw [Nat.sub_add_cancel hq]
    · simp [hx]

end Omega.EA
