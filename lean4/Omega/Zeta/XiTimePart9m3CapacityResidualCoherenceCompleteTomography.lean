import Omega.Zeta.XiOracleCapacityLayercakeTailCompleteness

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label:
`thm:xi-time-part9m3-capacity-residual-coherence-complete-tomography`. -/
theorem paper_xi_time_part9m3_capacity_residual_coherence_complete_tomography
    (d : Multiset Nat) :
    (∀ k : Nat, 1 <= k ->
      d.count k = (d.filter fun n => k <= n).card -
        (d.filter fun n => k + 1 <= n).card) ∧
      (∀ T : Nat, (d.map fun n => Nat.min n T).sum =
        ∑ k ∈ Finset.Icc 1 T, (d.filter fun n => k <= n).card) ∧
      (∀ q : Nat, (d.map fun n => n ^ q).sum =
        ∑ k ∈ d.toFinset, d.count k * k ^ q) := by
  classical
  rcases paper_xi_oracle_capacity_layercake_tail_completeness d with
    ⟨hcapacity, _htail, hcount⟩
  refine ⟨hcount, hcapacity, ?_⟩
  intro q
  simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    Finset.sum_multiset_map_count d (fun n => n ^ q)

end Omega.Zeta
