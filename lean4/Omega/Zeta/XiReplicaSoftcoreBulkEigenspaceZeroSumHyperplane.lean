import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-replica-softcore-bulk-eigenspace-zero-sum-hyperplane`. -/
theorem paper_xi_replica_softcore_bulk_eigenspace_zero_sum_hyperplane
    {ι K : Type*} [Fintype ι] [Field K] (c : K) (hc : c ≠ 0) :
    {a : ι → K | (∑ i, a i * c) = 0} = {a : ι → K | (∑ i, a i) = 0} := by
  ext a
  constructor
  · intro h
    have hmul : (∑ i, a i) * c = 0 := by
      simpa [Finset.sum_mul] using h
    exact (mul_eq_zero.mp hmul).resolve_right hc
  · intro h
    change (∑ i, a i) = 0 at h
    calc
      (∑ i, a i * c) = (∑ i, a i) * c := by rw [Finset.sum_mul]
      _ = 0 := by simp [h]

end Omega.Zeta
