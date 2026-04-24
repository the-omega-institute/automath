import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.POM.EscortMaxfiberTvBound
import Omega.POM.FiniteZeroTempEscortUniformMaxfiber
import Omega.Zeta.DerivedFixedFreezingRenyiSurface

namespace Omega.Conclusion

/-- Concrete order package for the all-axes freezing-measure collapse theorem. The registered
orders are required to be exactly the audited fixed-freezing orders. -/
structure conclusion_freezing_measure_collapse_all_axes_data where
  conclusion_freezing_measure_collapse_all_axes_registeredOrders : Finset ℕ
  conclusion_freezing_measure_collapse_all_axes_registeredOrders_eq :
    conclusion_freezing_measure_collapse_all_axes_registeredOrders =
      Omega.Zeta.derivedFixedFreezingOrders

/-- Trivial maximal multiplicity used to specialize the escort/max-fiber TV bound to the concrete
frozen three-state model. -/
def conclusion_freezing_measure_collapse_all_axes_Dm
    (_D : conclusion_freezing_measure_collapse_all_axes_data) : ℕ :=
  1

/-- The concrete frozen model simultaneously satisfies the exact missing-mass identity, the
escort/max-fiber TV bound, the bounded-observable collapse, and the all-order R\'enyi collapse on
the registered set of orders. -/
def conclusion_freezing_measure_collapse_all_axes_statement
    (D : conclusion_freezing_measure_collapse_all_axes_data) : Prop :=
  D.conclusion_freezing_measure_collapse_all_axes_registeredOrders =
      Omega.Zeta.derivedFixedFreezingOrders ∧
    Omega.Zeta.derivedFixedFreezingTvData.tvDistance =
      1 - Omega.Zeta.derivedFixedFreezingTvData.massOnMaxFiber ∧
    Omega.Zeta.derivedFixedFreezingTvData.tvDistance ≤
      Real.exp (-Omega.Zeta.derivedFixedFreezingTvData.exponentialGap) ∧
    Omega.Zeta.derivedFixedFreezingTvData.tvDistance ≤
      (conclusion_freezing_measure_collapse_all_axes_Dm D : ℝ) ^ (2 : ℕ) ∧
    Omega.Zeta.XiFixedFreezingEscortObservableData.exponentialObservableCollapse
      Omega.Zeta.derivedFixedFreezingObservableData ∧
    ∀ r ∈ D.conclusion_freezing_measure_collapse_all_axes_registeredOrders,
      Omega.Zeta.derivedFixedFreezingEntropyRateLimit r = Omega.Zeta.derivedFixedFreezingGStar

/-- Paper label: `thm:conclusion-freezing-measure-collapse-all-axes`. The concrete frozen
three-state model already carries the exact frozen missing-mass identity and its TV bound, the
bounded-observable collapse, and the collapse of every registered R\'enyi axis to the common
frozen value `g_* = 0`. -/
theorem paper_conclusion_freezing_measure_collapse_all_axes
    (D : conclusion_freezing_measure_collapse_all_axes_data) :
    conclusion_freezing_measure_collapse_all_axes_statement D := by
  have htv_identity := Omega.Zeta.paper_derived_fixed_freezing_microcanonical_tv
  have hescort_bound :
      Omega.Zeta.derivedFixedFreezingTvData.tvDistance ≤
        (conclusion_freezing_measure_collapse_all_axes_Dm D : ℝ) ^ (2 : ℕ) := by
    let hEscort : Omega.POM.EscortMaxfiberTvBoundData := {
      α := Fin 3
      instFintype := inferInstance
      instDecEq := inferInstance
      baseWeight := Omega.Zeta.derivedFixedFreezingEscortLaw
      fiberMultiplicity := fun _ => 1
      Dm := conclusion_freezing_measure_collapse_all_axes_Dm D
      tvDistance := Omega.Zeta.derivedFixedFreezingTvData.tvDistance
      denominatorBound := 0
      tvAsMissingMass := by
        simp [Omega.Zeta.derivedFixedFreezingTvData, Omega.POM.offMaxFiberSubset,
          Omega.POM.maximalFiberSubset, Omega.POM.escortWeight,
          conclusion_freezing_measure_collapse_all_axes_Dm]
      missingMassLeDenominator := by
        simp [Omega.POM.offMaxFiberSubset, Omega.POM.maximalFiberSubset, Omega.POM.escortWeight,
          conclusion_freezing_measure_collapse_all_axes_Dm]
      denominatorLeDmSq := by
        norm_num [conclusion_freezing_measure_collapse_all_axes_Dm]
    }
    simpa using Omega.POM.paper_pom_escort_maxfiber_tv_bound hEscort
  have hrenyi := Omega.Zeta.paper_derived_fixed_freezing_renyi_surface
  refine ⟨D.conclusion_freezing_measure_collapse_all_axes_registeredOrders_eq, htv_identity.1,
    htv_identity.2.1, hescort_bound, htv_identity.2.2, ?_⟩
  intro r hr
  rw [D.conclusion_freezing_measure_collapse_all_axes_registeredOrders_eq] at hr
  exact hrenyi r hr

end Omega.Conclusion
