import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Omega.Conclusion.BinfoldGaugeCenterEventualTriviality
import Omega.Conclusion.BinfoldRenyiRateCollapse
import Omega.Conclusion.BinfoldTailOrderStatisticsSingleJumpCollapse
import Omega.Conclusion.BinfoldTwoAtomInformationGeometryUniversality

open Filter

namespace Omega.Conclusion

/-- The strict nonsaturation region is modeled by eventual triviality of the bin-fold gauge
center, i.e. the maximal fiber bound is no longer attained. -/
def conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_strict_nonsaturation
    (m : ℕ) : Prop :=
  ∀ z : binfoldGaugeCenter m, z = 1

/-- The two-atom limit law at stage `m`, specialized to the identity observable. -/
def conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_twoatom_limit_law
    (m : ℕ) : Prop :=
  foldbinLikelihoodRatioExpectation m (fun x : ℝ => x) =
    binfoldTwoPointLimitMassHigh Real.goldenRatio m * foldbinLikelihoodRatioLow m +
      binfoldTwoPointLimitMassLow Real.goldenRatio m * foldbinLikelihoodRatioHigh m

/-- The tail single-jump law is the conclusion-level threshold statement, independent of `m`. -/
def conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_tail_single_jump_law
    (_m : ℕ) : Prop :=
  conclusion_binfold_tail_order_statistics_single_jump_collapse_statement

/-- The Renyi rate collapse specialized to the positive order `q = m + 1`. -/
def conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_renyi_rate_collapse
    (m : ℕ) : Prop :=
  Tendsto (Omega.Folding.foldBinRenyiEntropyRate ((m : ℝ) + 1)) atTop
    (nhds (Real.log Real.goldenRatio))

local notation "conclusion_binfold_strict_nonsaturation" =>
  conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_strict_nonsaturation

local notation "conclusion_binfold_twoatom_limit_law" =>
  conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_twoatom_limit_law

local notation "conclusion_binfold_tail_single_jump_law" =>
  conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_tail_single_jump_law

local notation "conclusion_binfold_renyi_rate_collapse" =>
  conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_renyi_rate_collapse

/-- Paper label: `thm:conclusion-binfold-twoatom-persistence-in-strict-nonsaturation-region`. The
finite set of saturated scales is absorbed into a common threshold; beyond it, the strict
nonsaturation statement and the three asymptotic two-atom laws hold simultaneously. -/
theorem paper_conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region :
    ∃ M : ℕ, ∀ m ≥ M,
      conclusion_binfold_strict_nonsaturation m ∧
        conclusion_binfold_twoatom_limit_law m ∧
        conclusion_binfold_tail_single_jump_law m ∧
        conclusion_binfold_renyi_rate_collapse m := by
  rcases paper_conclusion_binfold_gauge_center_eventual_triviality with ⟨_, hcenter⟩
  rcases hcenter with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro m hm
  refine ⟨hM m hm, ?_, ?_, ?_⟩
  · simpa [conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_twoatom_limit_law]
      using
        paper_conclusion_binfold_twoatom_information_geometry_universality m (fun x : ℝ => x)
  · exact paper_conclusion_binfold_tail_order_statistics_single_jump_collapse
  · simpa [conclusion_binfold_twoatom_persistence_in_strict_nonsaturation_region_renyi_rate_collapse]
      using paper_conclusion_binfold_renyi_rate_collapse ((m : ℝ) + 1) (by positivity)

end Omega.Conclusion
