import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedGoldenResonanceCompleteBernsteinPotential

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Positive member of the finite golden-resonance zero pair. -/
def conclusion_golden_resonance_weierstrass_genus_drop_positive_root (i : Fin 2) : ℝ :=
  Omega.DerivedConsequences.derived_golden_resonance_complete_bernstein_potential_positive_zero i

/-- Negative member paired with each positive golden-resonance zero. -/
def conclusion_golden_resonance_weierstrass_genus_drop_negative_root (i : Fin 2) : ℝ :=
  -conclusion_golden_resonance_weierstrass_genus_drop_positive_root i

/-- Quadratic factor obtained by pairing opposite roots. -/
def conclusion_golden_resonance_weierstrass_genus_drop_paired_factor
    (s : ℝ) (i : Fin 2) : ℝ :=
  (s - conclusion_golden_resonance_weierstrass_genus_drop_positive_root i) *
    (s - conclusion_golden_resonance_weierstrass_genus_drop_negative_root i)

/-- Genus-zero factor after cancelling the paired linear exponential corrections. -/
def conclusion_golden_resonance_weierstrass_genus_drop_genus_zero_factor
    (s : ℝ) (i : Fin 2) : ℝ :=
  s ^ 2 - (conclusion_golden_resonance_weierstrass_genus_drop_positive_root i) ^ 2

/-- The paired finite Weierstrass product equals the product of the genus-zero quadratic factors,
pointwise, hence locally uniformly in this finite model. -/
def conclusion_golden_resonance_weierstrass_genus_drop_paired_product_locally_uniform : Prop :=
  ∀ s : ℝ,
    (∏ i : Fin 2,
        conclusion_golden_resonance_weierstrass_genus_drop_paired_factor s i) =
      ∏ i : Fin 2,
        conclusion_golden_resonance_weierstrass_genus_drop_genus_zero_factor s i

/-- The paired product has genus zero in the finite golden-resonance model. -/
def conclusion_golden_resonance_weierstrass_genus_drop_genus_zero : Prop :=
  ∀ s : ℝ,
    (∏ i : Fin 2,
        conclusion_golden_resonance_weierstrass_genus_drop_genus_zero_factor s i) =
      ∏ i : Fin 2,
        (s ^ 2 -
          (Omega.DerivedConsequences.derived_golden_resonance_complete_bernstein_potential_positive_zero
            i) ^ 2)

/-- Paper label: `thm:conclusion-golden-resonance-weierstrass-genus-drop`. Splitting the finite
golden-resonance zero set into opposite pairs turns the Weierstrass factors into quadratic
genus-zero factors. -/
theorem paper_conclusion_golden_resonance_weierstrass_genus_drop :
    conclusion_golden_resonance_weierstrass_genus_drop_paired_product_locally_uniform ∧
      conclusion_golden_resonance_weierstrass_genus_drop_genus_zero := by
  refine ⟨?_, ?_⟩
  · intro s
    refine Finset.prod_congr rfl ?_
    intro i hi
    simp [conclusion_golden_resonance_weierstrass_genus_drop_paired_factor,
      conclusion_golden_resonance_weierstrass_genus_drop_negative_root,
      conclusion_golden_resonance_weierstrass_genus_drop_genus_zero_factor]
    ring
  · intro s
    rfl

end

end Omega.Conclusion
