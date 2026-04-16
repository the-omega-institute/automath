import Omega.EA.StableAddComputable

namespace Omega.EA

/-- Stable Zeckendorf arithmetic is computable because both operations have explicit normal-form
witnesses.
    prop:zeckendorf-arith-computable -/
theorem paper_zeckendorf_arith_computable {m : ℕ} (c d : Omega.X m) :
    (∃ s : Omega.X m, s = Omega.X.stableAdd c d) ∧
      ∃ p : Omega.X m, p = Omega.X.stableMul c d := by
  refine ⟨Omega.EA.StableAddComputable.paper_stable_add_computable m c d, ?_⟩
  exact ⟨Omega.X.stableMul c d, rfl⟩

end Omega.EA
