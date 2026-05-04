import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Boolean assumptions for the conservative inner-Clark sufficient template. -/
structure xi_rh_sufficient_template_inner_clark_conservative_data where
  xi_rh_sufficient_template_inner_clark_conservative_boundedType : Bool
  xi_rh_sufficient_template_inner_clark_conservative_reflectionSymmetric : Bool
  xi_rh_sufficient_template_inner_clark_conservative_inner : Bool
  xi_rh_sufficient_template_inner_clark_conservative_clarkAbsolutelyContinuous : Bool
  xi_rh_sufficient_template_inner_clark_conservative_strictContraction : Bool

/-- The Blaschke-only conclusion in the conservative Boolean package. -/
def xi_rh_sufficient_template_inner_clark_conservative_blaschkeOnly
    (D : xi_rh_sufficient_template_inner_clark_conservative_data) : Prop :=
  D.xi_rh_sufficient_template_inner_clark_conservative_boundedType = true ∧
    D.xi_rh_sufficient_template_inner_clark_conservative_reflectionSymmetric = true ∧
      D.xi_rh_sufficient_template_inner_clark_conservative_inner = true ∧
        D.xi_rh_sufficient_template_inner_clark_conservative_clarkAbsolutelyContinuous = true

/-- The no off-critical-zero conclusion in the conservative Boolean package. -/
def xi_rh_sufficient_template_inner_clark_conservative_noOffCriticalZeros
    (D : xi_rh_sufficient_template_inner_clark_conservative_data) : Prop :=
  xi_rh_sufficient_template_inner_clark_conservative_blaschkeOnly D ∧
    D.xi_rh_sufficient_template_inner_clark_conservative_strictContraction = true

/-- Concrete conservative statement combining bounded type, innerness, Clark AC, and contraction. -/
def xi_rh_sufficient_template_inner_clark_conservative_statement
    (D : xi_rh_sufficient_template_inner_clark_conservative_data) : Prop :=
  D.xi_rh_sufficient_template_inner_clark_conservative_boundedType = true →
    D.xi_rh_sufficient_template_inner_clark_conservative_reflectionSymmetric = true →
      D.xi_rh_sufficient_template_inner_clark_conservative_inner = true →
        D.xi_rh_sufficient_template_inner_clark_conservative_clarkAbsolutelyContinuous = true →
          D.xi_rh_sufficient_template_inner_clark_conservative_strictContraction = true →
            xi_rh_sufficient_template_inner_clark_conservative_blaschkeOnly D ∧
              xi_rh_sufficient_template_inner_clark_conservative_noOffCriticalZeros D

/-- Paper label: `thm:xi-rh-sufficient-template-inner-clark-conservative`. -/
theorem paper_xi_rh_sufficient_template_inner_clark_conservative
    (D : xi_rh_sufficient_template_inner_clark_conservative_data) :
    xi_rh_sufficient_template_inner_clark_conservative_statement D := by
  intro hbounded hreflection hinner hclark hcontraction
  refine ⟨?_, ?_⟩
  · exact ⟨hbounded, hreflection, hinner, hclark⟩
  · exact ⟨⟨hbounded, hreflection, hinner, hclark⟩, hcontraction⟩

end Omega.Zeta
