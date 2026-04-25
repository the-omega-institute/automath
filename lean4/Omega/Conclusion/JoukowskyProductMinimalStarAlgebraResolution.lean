import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.JoukowskyProductAnalyticBlindnessMinimalRadialSufficiency

namespace Omega.Conclusion

/-- Concrete radial-profile datum for the product Joukowsky family. -/
def conclusion_joukowsky_product_minimal_star_algebra_resolution_data (k : ℕ)
    (conclusion_joukowsky_product_minimal_star_algebra_resolution_radial_profile : Fin k → ℕ) :
    JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData where
  conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension := k
  conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_profile :=
    conclusion_joukowsky_product_minimal_star_algebra_resolution_radial_profile

/-- Paper label: `cor:conclusion-joukowsky-product-minimal-star-algebra-resolution`. The
coordinate radial observables already separate the `k`-parameter Joukowsky family, and any family
with fewer than `k` extra coordinates misses the cardinal lower bound forced by the radial
reconstruction theorem. -/
theorem paper_conclusion_joukowsky_product_minimal_star_algebra_resolution
    (k : ℕ)
    (conclusion_joukowsky_product_minimal_star_algebra_resolution_radial_profile : Fin k → ℕ) :
    let D :=
      conclusion_joukowsky_product_minimal_star_algebra_resolution_data k
        conclusion_joukowsky_product_minimal_star_algebra_resolution_radial_profile
    (∀ d : ℕ, d < conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count D →
        ¬ Fintype.card (Fin k) ≤ d) ∧
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count D =
        Fintype.card (Fin k) ∧
      Function.LeftInverse
        (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_reconstruction D)
        (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable D) ∧
      Function.Injective
        (conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_observable D) := by
  dsimp [conclusion_joukowsky_product_minimal_star_algebra_resolution_data]
  let D : JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyData :=
    { conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_dimension := k
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_radial_profile :=
        conclusion_joukowsky_product_minimal_star_algebra_resolution_radial_profile }
  have hD :
      JoukowskyProductAnalyticBlindnessMinimalRadialSufficiencyStatement D :=
    paper_conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency D
  rcases hD with ⟨_, _, hleft, hinj, hmin⟩
  refine ⟨?_, ?_, hleft, hinj⟩
  · intro d hd hcard
    have hk : k ≤ d := by
      simpa [Fintype.card_fin] using hcard
    have hd' : d < k := by
      simpa [D,
        conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count]
        using hd
    omega
  · simp [Fintype.card_fin,
      conclusion_joukowsky_product_analytic_blindness_minimal_radial_sufficiency_observable_count]

end Omega.Conclusion
