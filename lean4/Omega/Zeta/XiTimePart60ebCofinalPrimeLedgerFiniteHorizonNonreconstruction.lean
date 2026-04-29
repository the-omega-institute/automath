import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part60eb-cofinal-prime-ledger-finite-horizon-nonreconstruction`. -/
theorem paper_xi_time_part60eb_cofinal_prime_ledger_finite_horizon_nonreconstruction
    {Prime Obs : Type} [DecidableEq Prime] (support : Obs → Finset Prime) (O : Finset Obs) :
    ∃ S0 : Finset Prime, (∀ o, o ∈ O → support o ⊆ S0) ∧
      (∀ chain : Nat → Finset Prime, (∀ n, S0 ⊆ chain n) → ∀ n o, o ∈ O →
        support o ⊆ chain n) := by
  let S0 : Finset Prime := O.biUnion support
  have hvisible : ∀ o, o ∈ O → support o ⊆ S0 := by
    intro o ho p hp
    exact Finset.mem_biUnion.mpr ⟨o, ho, hp⟩
  refine ⟨S0, hvisible, ?_⟩
  intro chain hchain n o ho
  exact (hvisible o ho).trans (hchain n)

end Omega.Zeta
