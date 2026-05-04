import Mathlib.Data.Countable.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- Concrete finite-winding certificate data: an uncountable connected torus component is read by
a finite vector of integer winding numbers. -/
structure conclusion_finite_winding_certificate_incompleteness_data where
  conclusion_finite_winding_certificate_incompleteness_Torus : Type u
  conclusion_finite_winding_certificate_incompleteness_torus_uncountable :
    Uncountable conclusion_finite_winding_certificate_incompleteness_Torus
  conclusion_finite_winding_certificate_incompleteness_M : ℕ
  conclusion_finite_winding_certificate_incompleteness_W :
    conclusion_finite_winding_certificate_incompleteness_Torus →
      Fin conclusion_finite_winding_certificate_incompleteness_M → ℤ

/-- The finite winding vector cannot distinguish all points of an uncountable torus component. -/
def conclusion_finite_winding_certificate_incompleteness_statement
    (D : conclusion_finite_winding_certificate_incompleteness_data) : Prop :=
  ∃ a a' : D.conclusion_finite_winding_certificate_incompleteness_Torus,
    a ≠ a' ∧
      D.conclusion_finite_winding_certificate_incompleteness_W a =
        D.conclusion_finite_winding_certificate_incompleteness_W a'

/-- Paper label: `prop:conclusion-finite-winding-certificate-incompleteness`. -/
theorem paper_conclusion_finite_winding_certificate_incompleteness
    (D : conclusion_finite_winding_certificate_incompleteness_data) :
    conclusion_finite_winding_certificate_incompleteness_statement D := by
  by_contra hcollision
  haveI : Uncountable D.conclusion_finite_winding_certificate_incompleteness_Torus :=
    D.conclusion_finite_winding_certificate_incompleteness_torus_uncountable
  have hInjective :
      Function.Injective D.conclusion_finite_winding_certificate_incompleteness_W := by
    intro a a' hW
    by_contra hne
    exact hcollision ⟨a, a', hne, hW⟩
  have hCountable :
      Countable D.conclusion_finite_winding_certificate_incompleteness_Torus :=
    hInjective.countable
  exact (Uncountable.not_countable
    (α := D.conclusion_finite_winding_certificate_incompleteness_Torus)) hCountable

end Omega.Conclusion
