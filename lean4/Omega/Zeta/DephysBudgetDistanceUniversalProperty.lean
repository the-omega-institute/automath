import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.DephysBudgetDistanceDominatesTv

namespace Omega.Zeta

/-- Concrete local wrapper for the universal property of the infimal dephysicalized budget
distance. The extra scalar `δ` is an arbitrary candidate pseudodistance already known to be
bounded by every feasible certificate budget. -/
structure dephys_budget_distance_universal_property_data where
  State : Type
  dephys_budget_distance_universal_property_instFintype : Fintype State
  dephys_budget_distance_universal_property_instNonempty : Nonempty State
  dephys_budget_distance_universal_property_instDecidableEq : DecidableEq State
  dephys_budget_distance_universal_property_x : State → Bool
  dephys_budget_distance_universal_property_y : State → Bool
  dephys_budget_distance_universal_property_delta : ℝ
  dephys_budget_distance_universal_property_feasible :
    (dephys_budget_distance_dominates_tv_budgetSet
      dephys_budget_distance_universal_property_x
      dephys_budget_distance_universal_property_y).Nonempty
  dephys_budget_distance_universal_property_delta_le_certificate :
    ∀ ε,
      dephys_budget_distance_dominates_tv_certificateChain
          dephys_budget_distance_universal_property_x
          dephys_budget_distance_universal_property_y ε →
        dephys_budget_distance_universal_property_delta ≤ ε

namespace dephys_budget_distance_universal_property_data

attribute [instance] dephys_budget_distance_universal_property_instFintype
attribute [instance] dephys_budget_distance_universal_property_instNonempty
attribute [instance] dephys_budget_distance_universal_property_instDecidableEq

/-- The local infimal budget distance. -/
noncomputable def dephys_budget_distance_universal_property_infimalDistance
    (D : dephys_budget_distance_universal_property_data) : ℝ :=
  dephys_budget_distance_dominates_tv_distance
    D.dephys_budget_distance_universal_property_x
    D.dephys_budget_distance_universal_property_y

/-- The infimal certificate budget dominates TV, is below every feasible budget, and dominates
every other candidate bounded by all feasible budgets. -/
def dephys_budget_distance_universal_property_holds
    (D : dephys_budget_distance_universal_property_data) : Prop :=
  dephys_eps_sound_dominates_tv_totalVariation
      D.dephys_budget_distance_universal_property_x
      D.dephys_budget_distance_universal_property_y ≤
    D.dephys_budget_distance_universal_property_infimalDistance ∧
  (∀ ε,
    dephys_budget_distance_dominates_tv_certificateChain
        D.dephys_budget_distance_universal_property_x
        D.dephys_budget_distance_universal_property_y ε →
      D.dephys_budget_distance_universal_property_infimalDistance ≤ ε) ∧
  D.dephys_budget_distance_universal_property_delta ≤
    D.dephys_budget_distance_universal_property_infimalDistance

end dephys_budget_distance_universal_property_data

open dephys_budget_distance_universal_property_data

/-- Paper label: `prop:dephys-budget-distance-universal-property`. The certificate-chain budget
distance is the infimum of all feasible budgets, hence it dominates TV, lies below each feasible
budget, and is the maximal candidate bounded by every feasible budget. -/
theorem paper_dephys_budget_distance_universal_property
    (D : dephys_budget_distance_universal_property_data) :
    D.dephys_budget_distance_universal_property_holds := by
  classical
  have htv :=
    paper_dephys_budget_distance_dominates_tv
      D.dephys_budget_distance_universal_property_x
      D.dephys_budget_distance_universal_property_y
      D.dephys_budget_distance_universal_property_feasible
  refine ⟨htv.1, ?_, ?_⟩
  · intro ε hε
    simp [dephys_budget_distance_universal_property_infimalDistance,
      dephys_budget_distance_dominates_tv_distance,
      dif_pos D.dephys_budget_distance_universal_property_feasible]
    exact csInf_le
      ⟨D.dephys_budget_distance_universal_property_delta,
        fun ε hε' =>
          D.dephys_budget_distance_universal_property_delta_le_certificate ε hε'⟩
      hε
  · simp [dephys_budget_distance_universal_property_infimalDistance,
      dephys_budget_distance_dominates_tv_distance,
      dif_pos D.dephys_budget_distance_universal_property_feasible]
    exact le_csInf D.dephys_budget_distance_universal_property_feasible
      (fun ε hε =>
        D.dephys_budget_distance_universal_property_delta_le_certificate ε hε)

end Omega.Zeta
