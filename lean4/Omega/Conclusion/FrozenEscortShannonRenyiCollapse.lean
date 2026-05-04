import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Omega.Conclusion.FrozenEscortAllRenyiCollapse
import Omega.Conclusion.FrozenEscortIntegerRenyiCollapse
import Omega.Conclusion.MicroescortFrozenMinentropyRate
import Omega.Conclusion.NearCompleteRecoveryAboveSecondMaximum

open Filter

namespace Omega.Conclusion

noncomputable section

/-- Concrete data wrapper for the frozen escort Shannon--Renyi collapse.

It combines the pressure-line identities, max-fiber concentration defect, Renyi-rate collapse
package, and the Shannon/min-entropy rate locks as concrete numerical hypotheses. -/
structure conclusion_frozen_escort_shannon_renyi_collapse_data where
  conclusion_frozen_escort_shannon_renyi_collapse_pressure : ℝ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_a : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_ac : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_alpha_star : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_g_star : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_above_threshold :
    conclusion_frozen_escort_shannon_renyi_collapse_ac <
      conclusion_frozen_escort_shannon_renyi_collapse_a
  conclusion_frozen_escort_shannon_renyi_collapse_pressure_at_a :
    conclusion_frozen_escort_shannon_renyi_collapse_pressure
        conclusion_frozen_escort_shannon_renyi_collapse_a =
      conclusion_frozen_escort_shannon_renyi_collapse_a *
          conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
        conclusion_frozen_escort_shannon_renyi_collapse_g_star
  conclusion_frozen_escort_shannon_renyi_collapse_pressure_at_integer_multiple :
    ∀ b : ℕ,
      2 ≤ b →
        conclusion_frozen_escort_shannon_renyi_collapse_pressure
            (conclusion_frozen_escort_shannon_renyi_collapse_a * (b : ℝ)) =
          (conclusion_frozen_escort_shannon_renyi_collapse_a * (b : ℝ)) *
              conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
            conclusion_frozen_escort_shannon_renyi_collapse_g_star
  conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit :
    Option ℝ → ℝ → Prop
  conclusion_frozen_escort_shannon_renyi_collapse_renyi_one :
    conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit (some 1)
      conclusion_frozen_escort_shannon_renyi_collapse_g_star
  conclusion_frozen_escort_shannon_renyi_collapse_renyi_finite :
    ∀ s : ℝ,
      1 < s →
        conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit (some s)
          conclusion_frozen_escort_shannon_renyi_collapse_g_star
  conclusion_frozen_escort_shannon_renyi_collapse_renyi_infty :
    conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit none
      conclusion_frozen_escort_shannon_renyi_collapse_g_star
  conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_mass : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_identity :
    ∀ m : ℕ,
      conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_mass m =
        1 - conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect m
  conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect_zero :
    Tendsto conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect atTop
      (nhds 0)
  conclusion_frozen_escort_shannon_renyi_collapse_shannon_seq : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate_limit :
    Tendsto conclusion_frozen_escort_shannon_renyi_collapse_shannon_seq atTop
      (nhds conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate)
  conclusion_frozen_escort_shannon_renyi_collapse_shannon_frozen_limit :
    Tendsto conclusion_frozen_escort_shannon_renyi_collapse_shannon_seq atTop
      (nhds conclusion_frozen_escort_shannon_renyi_collapse_g_star)
  conclusion_frozen_escort_shannon_renyi_collapse_micro_rate : ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_max_micro_mass : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_auxiliary_K : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_auxiliary_M : ℕ → ℝ
  conclusion_frozen_escort_shannon_renyi_collapse_micro_rate_limit :
    Tendsto
      (fun m : ℕ =>
        -Real.log
            (conclusion_frozen_escort_shannon_renyi_collapse_max_micro_mass m) /
          (m : ℝ))
      atTop (nhds conclusion_frozen_escort_shannon_renyi_collapse_micro_rate)
  conclusion_frozen_escort_shannon_renyi_collapse_micro_frozen_limit :
    Tendsto
      (fun m : ℕ =>
        -Real.log
            (conclusion_frozen_escort_shannon_renyi_collapse_max_micro_mass m) /
          (m : ℝ))
      atTop
        (nhds
          (conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
            conclusion_frozen_escort_shannon_renyi_collapse_g_star))

namespace conclusion_frozen_escort_shannon_renyi_collapse_data

/-- Integer-order Renyi rates collapse on the frozen pressure line. -/
def conclusion_frozen_escort_shannon_renyi_collapse_integer_rates
    (D : conclusion_frozen_escort_shannon_renyi_collapse_data) : Prop :=
  ∀ b : ℕ,
    2 ≤ b →
      (D.conclusion_frozen_escort_shannon_renyi_collapse_pressure
            (D.conclusion_frozen_escort_shannon_renyi_collapse_a * (b : ℝ)) -
          (b : ℝ) *
            D.conclusion_frozen_escort_shannon_renyi_collapse_pressure
              D.conclusion_frozen_escort_shannon_renyi_collapse_a) /
        (1 - (b : ℝ)) =
        D.conclusion_frozen_escort_shannon_renyi_collapse_g_star

/-- Paper-facing statement for pressure freezing, concentration, and Shannon--Renyi collapse. -/
def conclusion_frozen_escort_shannon_renyi_collapse_statement
    (D : conclusion_frozen_escort_shannon_renyi_collapse_data) : Prop :=
  D.conclusion_frozen_escort_shannon_renyi_collapse_pressure
        D.conclusion_frozen_escort_shannon_renyi_collapse_a =
      D.conclusion_frozen_escort_shannon_renyi_collapse_a *
          D.conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
        D.conclusion_frozen_escort_shannon_renyi_collapse_g_star ∧
    Tendsto D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_mass atTop
      (nhds 1) ∧
      D.conclusion_frozen_escort_shannon_renyi_collapse_integer_rates ∧
        ((∀ s : ℝ,
            1 ≤ s →
              D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit
                (some s) D.conclusion_frozen_escort_shannon_renyi_collapse_g_star) ∧
          D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit none
            D.conclusion_frozen_escort_shannon_renyi_collapse_g_star) ∧
          D.conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate =
            D.conclusion_frozen_escort_shannon_renyi_collapse_g_star ∧
            D.conclusion_frozen_escort_shannon_renyi_collapse_micro_rate =
              D.conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
                D.conclusion_frozen_escort_shannon_renyi_collapse_g_star

end conclusion_frozen_escort_shannon_renyi_collapse_data

open conclusion_frozen_escort_shannon_renyi_collapse_data

/-- Paper label: `thm:conclusion-frozen-escort-shannon-renyi-collapse`. -/
theorem paper_conclusion_frozen_escort_shannon_renyi_collapse
    (D : conclusion_frozen_escort_shannon_renyi_collapse_data) :
    conclusion_frozen_escort_shannon_renyi_collapse_statement D := by
  have hconcentration :
      Tendsto D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_mass atTop
        (nhds 1) :=
    paper_conclusion_near_complete_recovery_above_second_maximum
      D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_mass
      D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect
      D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_identity
      D.conclusion_frozen_escort_shannon_renyi_collapse_max_fiber_defect_zero
  have hinteger :
      D.conclusion_frozen_escort_shannon_renyi_collapse_integer_rates := by
    intro b hb
    exact
      paper_conclusion_frozen_escort_integer_renyi_collapse
        D.conclusion_frozen_escort_shannon_renyi_collapse_pressure
        D.conclusion_frozen_escort_shannon_renyi_collapse_a
        D.conclusion_frozen_escort_shannon_renyi_collapse_ac
        D.conclusion_frozen_escort_shannon_renyi_collapse_alpha_star
        D.conclusion_frozen_escort_shannon_renyi_collapse_g_star
        b
        hb
        D.conclusion_frozen_escort_shannon_renyi_collapse_above_threshold
        D.conclusion_frozen_escort_shannon_renyi_collapse_pressure_at_a
        (D.conclusion_frozen_escort_shannon_renyi_collapse_pressure_at_integer_multiple b hb)
  have hall :
      (∀ s : ℝ,
          1 ≤ s →
            D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit (some s)
              D.conclusion_frozen_escort_shannon_renyi_collapse_g_star) ∧
        D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit none
          D.conclusion_frozen_escort_shannon_renyi_collapse_g_star :=
    paper_conclusion_frozen_escort_all_renyi_collapse
      D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_rate_limit
      D.conclusion_frozen_escort_shannon_renyi_collapse_g_star
      D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_one
      D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_finite
      D.conclusion_frozen_escort_shannon_renyi_collapse_renyi_infty
  have hshannon :
      D.conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate =
        D.conclusion_frozen_escort_shannon_renyi_collapse_g_star :=
    tendsto_nhds_unique
      D.conclusion_frozen_escort_shannon_renyi_collapse_shannon_rate_limit
      D.conclusion_frozen_escort_shannon_renyi_collapse_shannon_frozen_limit
  have hmicro :
      D.conclusion_frozen_escort_shannon_renyi_collapse_micro_rate =
        D.conclusion_frozen_escort_shannon_renyi_collapse_alpha_star +
          D.conclusion_frozen_escort_shannon_renyi_collapse_g_star :=
    paper_conclusion_microescort_frozen_minentropy_rate
      D.conclusion_frozen_escort_shannon_renyi_collapse_alpha_star
      D.conclusion_frozen_escort_shannon_renyi_collapse_g_star
      D.conclusion_frozen_escort_shannon_renyi_collapse_micro_rate
      D.conclusion_frozen_escort_shannon_renyi_collapse_max_micro_mass
      D.conclusion_frozen_escort_shannon_renyi_collapse_auxiliary_K
      D.conclusion_frozen_escort_shannon_renyi_collapse_auxiliary_M
      D.conclusion_frozen_escort_shannon_renyi_collapse_micro_rate_limit
      D.conclusion_frozen_escort_shannon_renyi_collapse_micro_frozen_limit
  exact
    ⟨D.conclusion_frozen_escort_shannon_renyi_collapse_pressure_at_a,
      hconcentration, hinteger, hall, hshannon, hmicro⟩

end

end Omega.Conclusion
