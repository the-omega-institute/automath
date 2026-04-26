import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6AuditBudgetSplit
import Omega.Zeta.DerivedFixedFreezingRenyiSurface

namespace Omega.Conclusion

/-- Concrete endpoint budget at which the audited window-`6` capacity has already saturated. -/
structure conclusion_freezing_infinity_budget_noncommutation_data where
  budget : ℕ
  hbudget : 2 ≤ budget

/-- The frozen fixed-freezing side preserves the maximal-fiber geometry, whereas the saturated
infinite-budget endpoint remembers only the total microstate count `64`. -/
def conclusion_freezing_infinity_budget_noncommutation_statement
    (D : conclusion_freezing_infinity_budget_noncommutation_data) : Prop :=
  Omega.Zeta.derivedFixedFreezingTvData.massOnMaxFiber = 1 ∧
    Omega.Zeta.derivedFixedFreezingTvData.tvDistance =
      1 - Omega.Zeta.derivedFixedFreezingTvData.massOnMaxFiber ∧
    Omega.Zeta.derivedFixedFreezingTvData.tvDistance ≤
      Real.exp (-Omega.Zeta.derivedFixedFreezingTvData.exponentialGap) ∧
    Omega.Zeta.XiFixedFreezingEscortObservableData.exponentialObservableCollapse
      Omega.Zeta.derivedFixedFreezingObservableData ∧
    Omega.Zeta.derivedFixedFreezingMaxFiber.card = 2 ∧
    Omega.TypedAddressBiaxialCompletion.window6AuditCapacity D.budget = 64 ∧
    Omega.TypedAddressBiaxialCompletion.window6AuditCapacity D.budget = 8 * 2 + 4 * 3 + 9 * 4

/-- Paper label: `thm:conclusion-freezing-infinity-budget-noncommutation`. The concrete frozen
escort package keeps all mass on the two-point maximal fiber, while the saturated window-`6`
capacity endpoint at any budget `B ≥ 2` has already collapsed to the total mass `64 = Σ d`. -/
theorem paper_conclusion_freezing_infinity_budget_noncommutation
    (D : conclusion_freezing_infinity_budget_noncommutation_data) :
    conclusion_freezing_infinity_budget_noncommutation_statement D := by
  have hfreeze := Omega.Zeta.paper_derived_fixed_freezing_microcanonical_tv
  rcases
      Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_window6_audit_budget_split
    with ⟨_hcap, _h0, _h1, _h2, hsat, _hreplay, _hboundary, _hanomaly, _hgap1, _hgap2,
      _hinfty⟩
  have hcap64 : Omega.TypedAddressBiaxialCompletion.window6AuditCapacity D.budget = 64 :=
    (hsat D.budget).2 D.hbudget
  refine ⟨rfl, hfreeze.1, hfreeze.2.1, hfreeze.2.2, ?_, hcap64, ?_⟩
  · norm_num [Omega.Zeta.derivedFixedFreezingMaxFiber]
  · calc
      Omega.TypedAddressBiaxialCompletion.window6AuditCapacity D.budget = 64 := hcap64
      _ = 8 * 2 + 4 * 3 + 9 * 4 := by norm_num

end Omega.Conclusion
