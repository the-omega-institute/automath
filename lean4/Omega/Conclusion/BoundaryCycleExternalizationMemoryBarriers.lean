import Omega.Conclusion.PrimeIntegerizationSuperlinearBitlength
import Omega.SPG.BoundaryCycleRankFromEntropy
import Omega.SPG.BoundaryGaugeGroupoidCapacity
import Omega.SPG.FixedAxisGodelOrderInformation

namespace Omega.Conclusion

open Omega.SPG

/-- Concrete bookkeeping data for the conclusion-level boundary-cycle externalization barrier. The
fields record the entropy-to-cycle-rank input, a gauge-groupoid coverage inequality, a
prime-register injection, and a fixed-axis injection for the chosen register profile. -/
structure conclusion_boundary_cycle_externalization_memory_barriers_data where
  entropyDepth : ℕ
  boundaryEntropy : ℝ
  eulerCorrection : ℝ
  cycleRank : ℝ
  hlog2 : 0 < Real.log 2
  entropy_upper :
    boundaryEntropy ≤ 2 * Real.log 2 * (eulerCorrection / (2 : ℝ) ^ entropyDepth)
  cycle_rank_lower : eulerCorrection - eulerCorrection + 1 ≤ cycleRank
  queryComplexity : ℕ
  coarseLabels : ℕ
  gaugeAlphabet : ℕ
  bettiBase : ℕ
  bettiBarrier : ℕ
  coarseLabels_pos : 0 < coarseLabels
  gaugeAlphabet_gt_one : 1 < gaugeAlphabet
  betti_monotone : bettiBase ≤ bettiBarrier
  gauge_cover :
    2 ^ queryComplexity ≤ spgBoundaryGaugeCodeCard coarseLabels gaugeAlphabet bettiBase bettiBarrier
  primeAlphabet : ℕ
  registerDepth : ℕ
  axisCount : ℕ
  registerCeiling : ℕ
  prime_register_injective :
    ∃ f : Fin (primeAlphabet ^ registerDepth) → Fin ((registerCeiling + 1) ^ axisCount),
      Function.Injective f
  fixedAxisRegister : Fin axisCount → ℕ
  fixedAxisAlphabet : ℕ
  fixedAxisDepth : ℕ
  fixed_axis_injective :
    ∃ f : Fin (fixedAxisAlphabet ^ fixedAxisDepth) →
        Fin ((fixedAxisMaxExponent fixedAxisRegister + 1) ^ axisCount),
      Function.Injective f

/-- Conclusion-level externalization barrier: the entropy lower bound forces a cycle-rank/Betti
barrier, the gauge-groupoid cover forces a query-complexity barrier, the prime-register injection
forces a register budget barrier, the fixed-axis encoding forces an order-information barrier, and
the previously established scalar Gödel growth law remains available. -/
def conclusion_boundary_cycle_externalization_memory_barriers_statement
    (D : conclusion_boundary_cycle_externalization_memory_barriers_data) : Prop :=
  ((2 : ℝ) ^ D.entropyDepth / (2 * Real.log 2)) * D.boundaryEntropy -
      D.eulerCorrection + 1 ≤ D.cycleRank ∧
    (D.bettiBase : ℝ) +
        (((D.queryComplexity : ℝ) * Real.log 2 - Real.log D.coarseLabels) /
          Real.log D.gaugeAlphabet) ≤
      D.bettiBarrier ∧
    D.primeAlphabet ^ D.registerDepth ≤ (D.registerCeiling + 1) ^ D.axisCount ∧
    D.fixedAxisAlphabet ^ D.fixedAxisDepth ≤
      (fixedAxisMaxExponent D.fixedAxisRegister + 1) ^ D.axisCount ∧
    fixedAxisMaxExponent D.fixedAxisRegister ≤
      Nat.log 2 (fixedAxisGodelCode D.fixedAxisRegister) ∧
    conclusion_prime_integerization_superlinear_bitlength_statement

/-- Paper label:
`thm:conclusion-boundary-cycle-externalization-memory-barriers`. -/
theorem paper_conclusion_boundary_cycle_externalization_memory_barriers
    (D : conclusion_boundary_cycle_externalization_memory_barriers_data) :
    conclusion_boundary_cycle_externalization_memory_barriers_statement D := by
  have hcycle :
      ((2 : ℝ) ^ D.entropyDepth / (2 * Real.log 2)) * D.boundaryEntropy -
          D.eulerCorrection + 1 ≤
        D.cycleRank := by
    simpa using
      paper_spg_boundary_cycle_rank_from_entropy D.entropyDepth D.boundaryEntropy
        D.eulerCorrection D.eulerCorrection D.cycleRank D.hlog2 D.entropy_upper
        D.cycle_rank_lower
  have hgauge :=
    paper_spg_boundary_gauge_groupoid_capacity D.queryComplexity D.coarseLabels
      D.gaugeAlphabet D.bettiBase D.bettiBarrier D.coarseLabels_pos
      D.gaugeAlphabet_gt_one D.betti_monotone
  have hquery :
      (D.bettiBase : ℝ) +
          (((D.queryComplexity : ℝ) * Real.log 2 - Real.log D.coarseLabels) /
            Real.log D.gaugeAlphabet) ≤
        D.bettiBarrier := by
    exact hgauge.2.2 D.gauge_cover
  have hprime :
      D.primeAlphabet ^ D.registerDepth ≤ (D.registerCeiling + 1) ^ D.axisCount := by
    exact paper_spg_prime_register_budget_lower_bound D.primeAlphabet D.registerDepth
      D.axisCount D.registerCeiling D.prime_register_injective
  have hfixed :=
    paper_spg_fixed_axis_godel_order_information D.fixedAxisAlphabet D.fixedAxisDepth
      D.axisCount D.fixedAxisRegister D.fixed_axis_injective
  exact ⟨hcycle, hquery, hprime, hfixed.1, hfixed.2,
    paper_conclusion_prime_integerization_superlinear_bitlength⟩

end Omega.Conclusion
