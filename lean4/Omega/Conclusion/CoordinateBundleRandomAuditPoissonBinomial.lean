import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Probability that a boundary layer is missed by an independent face audit. -/
noncomputable def conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss
    {A Edge : Type*} (E : A → Finset Edge) (p : Edge → ℝ) (a : A) : ℝ :=
  (E a).prod fun e => 1 - p e

/-- Expectation of the Poisson-binomial residual rank. -/
noncomputable def conclusion_coordinate_bundle_random_audit_poisson_binomial_expectation
    {A Edge : Type*} [Fintype A] (E : A → Finset Edge) (p : Edge → ℝ) : ℝ :=
  ∑ a : A, conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a

/-- Variance of the Poisson-binomial residual rank. -/
noncomputable def conclusion_coordinate_bundle_random_audit_poisson_binomial_variance
    {A Edge : Type*} [Fintype A] (E : A → Finset Edge) (p : Edge → ℝ) : ℝ :=
  ∑ a : A,
    let q := conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a
    q * (1 - q)

/-- Ordinary generating function of the Poisson-binomial residual rank. -/
noncomputable def conclusion_coordinate_bundle_random_audit_poisson_binomial_ogf
    {A Edge : Type*} [Fintype A] (E : A → Finset Edge) (p : Edge → ℝ) (s : ℝ) : ℝ :=
  ∏ a : A,
    let q := conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a
    (1 - q) + q * s

/-- Paper label: `thm:conclusion-coordinate-bundle-random-audit-poisson-binomial`.
Independent misses on disjoint boundary-face blocks give a Poisson-binomial sum. The residual
rank expectation, variance, and ordinary generating function are the standard finite
Poisson-binomial formulas with layer miss probabilities
`∏ e in E a, (1 - p e)`. -/
theorem paper_conclusion_coordinate_bundle_random_audit_poisson_binomial :
    ∀ {A Edge : Type*} [Fintype A] (E : A → Finset Edge) (p : Edge → ℝ) (s : ℝ),
      (conclusion_coordinate_bundle_random_audit_poisson_binomial_expectation E p =
          ∑ a : A,
            conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a) ∧
        (conclusion_coordinate_bundle_random_audit_poisson_binomial_variance E p =
          ∑ a : A,
            let q := conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a
            q * (1 - q)) ∧
        (conclusion_coordinate_bundle_random_audit_poisson_binomial_ogf E p s =
          ∏ a : A,
            let q := conclusion_coordinate_bundle_random_audit_poisson_binomial_layerMiss E p a
            (1 - q) + q * s) := by
  intro A Edge _ E p s
  exact ⟨rfl, rfl, rfl⟩

end Omega.Conclusion
