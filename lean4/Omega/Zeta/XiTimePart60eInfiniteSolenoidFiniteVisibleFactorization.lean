import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part60e-infinite-solenoid-finite-visible-factorization`. -/
theorem paper_xi_time_part60e_infinite_solenoid_finite_visible_factorization
    {ι α : Type*} [Fintype ι] [DecidableEq α] (support : ι → Finset α) :
    ∃ S0 : Finset α, ∀ i : ι, support i ⊆ S0 := by
  refine ⟨Finset.univ.biUnion support, ?_⟩
  intro i a ha
  rw [Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, ha⟩

end Omega.Zeta
