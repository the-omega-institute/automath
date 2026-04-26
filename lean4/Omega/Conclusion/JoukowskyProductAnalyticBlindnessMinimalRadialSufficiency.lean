import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

structure JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData where
  conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension : ℕ
  conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_profile :
    Fin conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension → ℕ

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) : ℕ :=
  D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_coordinate_moment
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData)
    (i : Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension) :
    ℕ :=
  D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_profile i + 1

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_product_moment
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) : ℕ :=
  ∏ i :
      Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension,
    conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_coordinate_moment
      D i

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) :
    (Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension →
        ℕ) →
      Fin
          (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count
            D) →
        ℕ :=
  fun v => v

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_reconstruction
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) :
    (Fin
          (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count
            D) →
        ℕ) →
      Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension →
        ℕ :=
  fun obs => obs

def conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_minimality_bound
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) : Prop :=
  Fintype.card
      (Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension) ≤
    conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count D

def JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyStatement
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) : Prop :=
  conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_product_moment D =
    ∏ i :
        Fin D.conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension,
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_coordinate_moment
        D i ∧
    (∀ v i,
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_reconstruction
          D
          (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable
            D v) i =
        v i) ∧
    Function.LeftInverse
      (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_reconstruction
        D)
      (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable
        D) ∧
    Function.Injective
      (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable
        D) ∧
    conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_minimality_bound D

theorem paper_conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency
    (D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData) :
    JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyStatement D := by
  have conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_left_inverse :
      Function.LeftInverse
        (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_reconstruction
          D)
        (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable
          D) := by
    intro v
    funext i
    rfl
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro v i
    rfl
  · exact conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_left_inverse
  · exact Function.LeftInverse.injective
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_left_inverse
  · simp [conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_minimality_bound,
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count]

end Omega.Conclusion
