import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.SPG.PrimeRegisterBudgetLowerBound

namespace Omega.SPG

/-- Chapter-local data for the paper-facing statement that a fixed finite prime-register scheme
captures a vanishing fraction of distinguishable classes once the residual rank diverges. -/
structure PrimeRegisterDistinguishableFractionData where
  p : ℕ
  k : ℕ
  E : ℕ
  prime : Fact p.Prime
  residualRank : ℕ → ℕ
  distinguishableFraction : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ distinguishableFraction n
  le_budget_ratio :
    ∀ n, distinguishableFraction n ≤ ((E + 1 : ℝ) ^ k) / (p : ℝ) ^ residualRank n
  residualRankGrows : Filter.Tendsto residualRank Filter.atTop Filter.atTop

attribute [instance] PrimeRegisterDistinguishableFractionData.prime

/-- For a fixed finite-state prime-register scheme, the distinguishable fraction is bounded by a
constant numerator over the full fiber size `p ^ r(f)` and therefore tends to `0` once
`r(f) → ∞`.
    cor:spg-prime-register-distinguishable-fraction-vanishes -/
theorem paper_spg_prime_register_distinguishable_fraction_vanishes
    (D : PrimeRegisterDistinguishableFractionData) :
    Filter.Tendsto D.distinguishableFraction Filter.atTop (nhds 0) := by
  have hp : 1 < (D.p : ℝ) := by
    exact_mod_cast D.prime.out.one_lt
  have hdenom :
      Filter.Tendsto (fun n => (D.p : ℝ) ^ D.residualRank n) Filter.atTop Filter.atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt hp).comp D.residualRankGrows
  have hratio :
      Filter.Tendsto
        (fun n => ((D.E + 1 : ℝ) ^ D.k) / (D.p : ℝ) ^ D.residualRank n)
        Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
    D.nonneg D.le_budget_ratio

end Omega.SPG
