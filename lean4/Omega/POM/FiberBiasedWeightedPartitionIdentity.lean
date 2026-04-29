import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete parameters for the biased Boolean-cube fiber partition identity. -/
structure pom_fiber_biased_weighted_partition_identity_data where
  pom_fiber_biased_weighted_partition_identity_rank : ℕ
  pom_fiber_biased_weighted_partition_identity_bias : ℝ

/-- Hamming weight of a Boolean cube point. -/
def pom_fiber_biased_weighted_partition_identity_hammingWeight {n : ℕ}
    (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i).card

/-- Bernoulli product weight attached to a Boolean cube point. -/
noncomputable def pom_fiber_biased_weighted_partition_identity_cubeWeight (p : ℝ) {n : ℕ}
    (x : Fin n → Bool) : ℝ :=
  p ^ pom_fiber_biased_weighted_partition_identity_hammingWeight x *
    (1 - p) ^ (n - pom_fiber_biased_weighted_partition_identity_hammingWeight x)

/-- The total biased weight in the Hamming-weight fiber `k`. -/
noncomputable def pom_fiber_biased_weighted_partition_identity_fiberWeight (n : ℕ)
    (p : ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sum fun x : Fin n → Bool =>
    if pom_fiber_biased_weighted_partition_identity_hammingWeight x = k then
      pom_fiber_biased_weighted_partition_identity_cubeWeight p x
    else
      0

/-- The finite fiber partition identity on the Boolean cube. -/
def pom_fiber_biased_weighted_partition_identity_statement
    (D : pom_fiber_biased_weighted_partition_identity_data) : Prop :=
  (Finset.range
      (D.pom_fiber_biased_weighted_partition_identity_rank + 1)).sum
      (fun k =>
        pom_fiber_biased_weighted_partition_identity_fiberWeight
        D.pom_fiber_biased_weighted_partition_identity_rank
        D.pom_fiber_biased_weighted_partition_identity_bias k) =
    Finset.univ.sum
      (fun x : Fin D.pom_fiber_biased_weighted_partition_identity_rank → Bool =>
        pom_fiber_biased_weighted_partition_identity_cubeWeight
          D.pom_fiber_biased_weighted_partition_identity_bias x)

/-- Paper label: `thm:pom-fiber-biased-weighted-partition-identity`. -/
theorem paper_pom_fiber_biased_weighted_partition_identity
    (D : pom_fiber_biased_weighted_partition_identity_data) :
    pom_fiber_biased_weighted_partition_identity_statement D := by
  classical
  unfold pom_fiber_biased_weighted_partition_identity_statement
    pom_fiber_biased_weighted_partition_identity_fiberWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _
  let n := D.pom_fiber_biased_weighted_partition_identity_rank
  let w :=
    pom_fiber_biased_weighted_partition_identity_hammingWeight
      (n := n) x
  have hw_le : w ≤ n := by
    dsimp [w, pom_fiber_biased_weighted_partition_identity_hammingWeight]
    simpa using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => x i))
  have hw_mem : w ∈ Finset.range (n + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hw_le)
  have hsingle :
      (Finset.range (n + 1)).sum (fun k =>
          if pom_fiber_biased_weighted_partition_identity_hammingWeight x = k then
            pom_fiber_biased_weighted_partition_identity_cubeWeight
              D.pom_fiber_biased_weighted_partition_identity_bias x
          else
            0) =
        pom_fiber_biased_weighted_partition_identity_cubeWeight
          D.pom_fiber_biased_weighted_partition_identity_bias x := by
    rw [Finset.sum_eq_single w]
    · dsimp [w]
      simp
    · intro k _ hk
      have hk' :
          pom_fiber_biased_weighted_partition_identity_hammingWeight x ≠ k := by
        intro h
        exact hk (by simpa [w] using h.symm)
      simp [hk']
    · intro hw_not_mem
      exact False.elim (hw_not_mem hw_mem)
  simpa [n] using hsingle

end Omega.POM
