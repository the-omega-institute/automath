import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Omega.Conclusion.S4BoundaryTotalTorusRankConservation

namespace Omega.Conclusion

/-- The recorded Prym polarization type attached to the universal `ρ₃'` boundary carrier. -/
def conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type : List ℕ :=
  [1, 1, 1, 1, 2, 2, 2, 2, 2]

/-- The product polarization type on `P^3`, obtained by repeating the Prym type three times. -/
def conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_product_type : List ℕ :=
  conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ++
    conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ++
    conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type

/-- A polarization type is principal exactly when every elementary divisor is `1`. -/
def conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_is_principal
    (polarizationType : List ℕ) : Prop :=
  ∀ d ∈ polarizationType, d = 1

/-- Paper label: `thm:conclusion-s4-universal-boundary-carrier-nonprincipal-polarization`. -/
theorem paper_conclusion_s4_universal_boundary_carrier_nonprincipal_polarization :
    (∃! f : S4BoundaryFactor,
      (∀ r : S4BoundaryType, appearsInMain f r) ∧ (∀ r : S4BoundaryType, 0 < torusRank f r)) ∧
    conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type =
      [1, 1, 1, 1, 2, 2, 2, 2, 2] ∧
    ¬ conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_is_principal
        conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ∧
    conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_product_type =
      conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ++
        conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ++
        conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type ∧
    ¬ conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_is_principal
        conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_product_type := by
  refine ⟨paper_conclusion_s4_rho3prime_unique_universal_boundary_carrier, rfl, ?_, rfl, ?_⟩
  · intro hprincipal
    have htwo : (2 : ℕ) = 1 := by
      exact hprincipal 2 (by simp [conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type])
    omega
  · intro hprincipal
    have htwo : (2 : ℕ) = 1 := by
      exact hprincipal 2 (by
        simp [conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_product_type,
          conclusion_s4_universal_boundary_carrier_nonprincipal_polarization_prym_type])
    omega

end Omega.Conclusion
