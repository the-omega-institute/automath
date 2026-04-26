import Mathlib.Tactic
import Omega.POM.ZeroAnomPullbackExactness

namespace Omega.POM

/-- Concrete interface data for the `E_m`/lift residual swap. The scalar residual is shared with
the zero-anomaly pullback wrapper, while the residual support records the twist channels on which
the remaining obstruction can live. -/
structure pom_em_lift_residual_swap_data where
  pom_em_lift_residual_swap_zero_data : pom_zero_anom_pullback_exactness_data
  pom_em_lift_residual_swap_zero_anomaly :
    pom_em_lift_residual_swap_zero_data.zeroAnomaly
  pom_em_lift_residual_swap_twist : Type*
  pom_em_lift_residual_swap_trivial_twist : pom_em_lift_residual_swap_twist
  pom_em_lift_residual_swap_residual_support : Set pom_em_lift_residual_swap_twist
  pom_em_lift_residual_swap_support_nontrivial :
    ∀ χ,
      χ ∈ pom_em_lift_residual_swap_residual_support →
        χ ≠ pom_em_lift_residual_swap_trivial_twist

namespace pom_em_lift_residual_swap_data

/-- Zero anomaly on the closed-loop residual is equivalent to Beck--Chevalley exactness, and the
interface records the zero-anomaly side. -/
def decoupled_zero_anomaly (D : pom_em_lift_residual_swap_data) : Prop :=
  D.pom_em_lift_residual_swap_zero_data.beckChevalleyExact ∧
    D.pom_em_lift_residual_swap_zero_data.zeroAnomaly

/-- Every supported residual twist is a nontrivial twist channel. -/
def residual_carried_by_nontrivial_twists (D : pom_em_lift_residual_swap_data) : Prop :=
  D.pom_em_lift_residual_swap_residual_support ⊆
    {χ | χ ≠ D.pom_em_lift_residual_swap_trivial_twist}

end pom_em_lift_residual_swap_data

/-- Paper label: `prop:pom-em-lift-residual-swap`. The concrete swap interface combines the
zero-anomaly pullback-exactness wrapper with the recorded support condition for nontrivial twist
residuals. -/
theorem paper_pom_em_lift_residual_swap (D : pom_em_lift_residual_swap_data) :
    D.decoupled_zero_anomaly ∧ D.residual_carried_by_nontrivial_twists := by
  constructor
  · constructor
    · exact
        (paper_pom_zero_anom_pullback_exactness
          D.pom_em_lift_residual_swap_zero_data).1 D.pom_em_lift_residual_swap_zero_anomaly
    · exact D.pom_em_lift_residual_swap_zero_anomaly
  · intro χ hχ
    exact D.pom_em_lift_residual_swap_support_nontrivial χ hχ

end Omega.POM
