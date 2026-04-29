import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinOracleCriticalProfile

open Filter
open scoped Topology goldenRatio

namespace Omega.Conclusion

noncomputable section

/-- Conclusion-level optimal `q`-energy density under the critical budget scaling. -/
noncomputable def conclusion_binfold_critical_budget_renyi_energy_density
    (_q B m : ℕ) : ℝ :=
  Omega.Folding.foldBinCriticalSucc m B

/-- Conclusion-level limiting phase function for the critical budget scaling. -/
noncomputable def conclusion_binfold_critical_budget_renyi_energy_limit
    (_q : ℕ) (tau : ℝ) : ℝ :=
  Omega.Folding.foldBinCriticalProfile tau

/-- Paper label: `thm:conclusion-binfold-critical-budget-renyi-energy`. The already verified
critical-profile theorem for the normalized budget `2^{B_m} / (2 / φ)^m` transports directly to
the conclusion-level `q`-energy density wrapper. -/
theorem paper_conclusion_binfold_critical_budget_renyi_energy (q : Nat) (hq : 1 <= q)
    (tau : Real) (htau : 0 < tau) (B : Nat -> Nat)
    (hB :
      Tendsto (fun m : Nat => ((2 : Real) ^ B m) / ((2 / Real.goldenRatio : Real) ^ m)) atTop
        (nhds tau)) :
    Tendsto (fun m : Nat => conclusion_binfold_critical_budget_renyi_energy_density q (B m) m)
      atTop (nhds (conclusion_binfold_critical_budget_renyi_energy_limit q tau)) := by
  have hprofile :
      Tendsto (fun m : ℕ => Omega.Folding.foldBinCriticalTau m (B m)) atTop (nhds tau) := by
    simpa [Omega.Folding.foldBinCriticalTau, Omega.Folding.foldBinOracleCriticalBase,
      Omega.Folding.foldBinTwoStateGrowth] using hB
  simpa [conclusion_binfold_critical_budget_renyi_energy_density,
    conclusion_binfold_critical_budget_renyi_energy_limit] using
    Omega.Folding.paper_conclusion_foldbin_oracle_critical_profile B tau (le_of_lt htau) hprofile

end

end Omega.Conclusion
