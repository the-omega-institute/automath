import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Xi-facing wrapper packaging the minimal ledger-cost lower bound and its witness. -/
theorem paper_xi_cdim_minimal_ledger_cost (f : Omega.CircleDimension.CircleDimHomData) :
    (∀ R_rank : Nat, f.kernelRank ≤ R_rank →
      Omega.CircleDimension.circleDim f.kernelRank 0 <=
        Omega.CircleDimension.circleDim R_rank 0) ∧
      (∃ R_rank : Nat,
        Omega.CircleDimension.circleDim R_rank 0 =
          Omega.CircleDimension.circleDim f.kernelRank 0) := by
  refine ⟨fun R_rank hR => cdim_min_ledger_cost f R_rank hR, ?_⟩
  rcases cdim_min_ledger_cost_attained f with ⟨R_rank, hR⟩
  exact ⟨R_rank, hR.symm⟩

end Omega.CircleDimension
