import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-joint-observable-minimal-conductor`. The joint
conductor of a finite observable family is the least common multiple of its individual
conductors. -/
theorem paper_conclusion_fibadic_joint_observable_minimal_conductor {ι : Type*} [Fintype ι]
    (N : ι → ℕ) (hpos : ∀ j, 0 < N j) :
    let L := Finset.lcm Finset.univ N
    (∀ j : ι, N j ∣ L) ∧
      (∀ M : ℕ, (∀ j : ι, N j ∣ M) → L ∣ M) := by
  intro L
  have _ := hpos
  constructor
  · intro j
    exact Finset.dvd_lcm (Finset.mem_univ j)
  · intro M hM
    exact Finset.lcm_dvd (fun j _ => hM j)

end Omega.Conclusion
