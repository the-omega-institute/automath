import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionCollisionExponent

namespace Omega.POM

noncomputable section

/-- Collision probability of the multiplicity-composition law in the `q = 2` channel. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability
    (L : ℕ) : ℝ :=
  pomMomentHierarchyPartition 2 L / (pomMomentHierarchyPartition 1 L) ^ (2 : Nat)

/-- Cardinality normalization for the uniform measure on length-`L` compositions. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_uniformNormalization
    (L : ℕ) : ℝ :=
  (2 : ℝ) ^ (L - 1)

/-- Base-`2` logarithm used for the Rényi-`2` divergence statement. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Rényi-`2` divergence from the composition law to the uniform law. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_divergence
    (L : ℕ) : ℝ :=
  pom_multiplicity_composition_renyi2_divergence_to_uniform_log2
    (pom_multiplicity_composition_renyi2_divergence_to_uniform_uniformNormalization L *
      pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability L)

/-- The closed base-`2` collision exponent inherited from the two-copy collision theorem. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionExponentBase2 : ℝ :=
  pom_multiplicity_composition_renyi2_divergence_to_uniform_log2
    ((pomMultiplicityCompositionLambda 1) ^ (2 : Nat) / pomMultiplicityCompositionLambda 2)

/-- The corresponding divergence-rate normalization against the uniform composition measure. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_rate : ℝ :=
  1 - pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionExponentBase2

/-- Paper-facing statement for the uniform Rényi-`2` divergence package. -/
def pom_multiplicity_composition_renyi2_divergence_to_uniform_statement : Prop :=
  (∀ L : ℕ,
      pom_multiplicity_composition_renyi2_divergence_to_uniform_divergence L =
        pom_multiplicity_composition_renyi2_divergence_to_uniform_log2
          (pom_multiplicity_composition_renyi2_divergence_to_uniform_uniformNormalization L *
            pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability L)) ∧
    (∃ c_minus c_plus : ℝ,
      0 < c_minus ∧
        c_minus ≤ c_plus ∧
          ∃ N : ℕ,
            ∀ L ≥ N,
              c_minus *
                  (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                    (2 : Nat)) ^
                    L ≤
                pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability L ∧
                pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability L ≤
                  c_plus *
                    (pomMultiplicityCompositionLambda 2 / (pomMultiplicityCompositionLambda 1) ^
                      (2 : Nat)) ^
                      L) ∧
      pom_multiplicity_composition_renyi2_divergence_to_uniform_rate =
        1 - pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionExponentBase2

/-- Paper label: `cor:pom-multiplicity-composition-renyi2-divergence-to-uniform`. -/
theorem paper_pom_multiplicity_composition_renyi2_divergence_to_uniform :
    pom_multiplicity_composition_renyi2_divergence_to_uniform_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro L
    rfl
  · simpa [pom_multiplicity_composition_renyi2_divergence_to_uniform_collisionProbability]
      using paper_pom_multiplicity_composition_collision_exponent
  · rfl

end

end Omega.POM
