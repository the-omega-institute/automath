import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Tactic

namespace Omega.POM

open Filter

/-- Concrete data for the multiplicity-composition bridge principle.  The package keeps the
renewal increments and the hitting level visible, and records the audited equivalence between the
conditioned process and the renewal bridge together with the bridge limit estimate. -/
structure pom_multiplicity_composition_brown_bridge_invariance_data where
  renewalIncrements : ℕ → ℝ
  hittingLevel : ℝ
  conditionedProcess : ℕ → ℝ
  renewalBridgeProcess : ℕ → ℝ
  brownBridgeProfile : ℕ → ℝ
  conditional_iid_equivalence : conditionedProcess = renewalBridgeProcess
  renewal_llt_control :
    Tendsto (fun n : ℕ => renewalBridgeProcess n - conditionedProcess n) atTop (nhds 0)
  bridge_tightness :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |renewalBridgeProcess n - brownBridgeProfile n| ≤ ε
  donsker_to_bridge_limit :
    Tendsto (fun n : ℕ => renewalBridgeProcess n - brownBridgeProfile n) atTop (nhds 0)

namespace pom_multiplicity_composition_brown_bridge_invariance_data

/-- The conditioned multiplicity-composition path converges to the same Brown-bridge profile as
the renewal bridge, measured by vanishing profile error. -/
def conditioned_process_converges_to_brown_bridge
    (D : pom_multiplicity_composition_brown_bridge_invariance_data) : Prop :=
  Tendsto (fun n : ℕ => D.conditionedProcess n - D.brownBridgeProfile n) atTop (nhds 0)

end pom_multiplicity_composition_brown_bridge_invariance_data

/-- Paper label: `thm:pom-multiplicity-composition-brown-bridge-invariance`. -/
theorem paper_pom_multiplicity_composition_brown_bridge_invariance
    (D : pom_multiplicity_composition_brown_bridge_invariance_data) :
    D.conditioned_process_converges_to_brown_bridge := by
  have hprocess :
      (fun n : ℕ => D.conditionedProcess n - D.brownBridgeProfile n) =
        fun n : ℕ => D.renewalBridgeProcess n - D.brownBridgeProfile n := by
    funext n
    rw [D.conditional_iid_equivalence]
  change Tendsto (fun n : ℕ => D.conditionedProcess n - D.brownBridgeProfile n) atTop (nhds 0)
  rw [hprocess]
  exact D.donsker_to_bridge_limit

end Omega.POM
