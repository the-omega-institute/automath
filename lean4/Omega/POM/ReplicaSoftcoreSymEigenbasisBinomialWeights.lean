import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Symmetric-layer eigenvalue inherited from the Fibonacci tensor eigenbasis. -/
def pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_eigenvalue
    (q j : ℕ) : ℝ :=
  (1 - Real.goldenRatio) ^ j * Real.goldenRatio ^ (q - j)

/-- Multiplicity of the symmetric tensor-eigenbasis layer with exactly `j` negative modes. -/
def pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_weight
    (q j : ℕ) : ℝ :=
  Nat.choose q j

/-- Total mass of all binomially weighted symmetric layers. -/
def pom_replica_softcore_sym_eigenbasis_binomial_weights_total_mass
    (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1),
    pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_weight q j

/-- Product weight attached to the `j`th symmetric tensor-eigenbasis layer. -/
def pom_replica_softcore_sym_eigenbasis_binomial_weights_product_weight
    (q j : ℕ) : ℝ :=
  pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_weight q j *
    pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_eigenvalue q j

/-- Paper-facing wrapper collecting the layer eigenvalue, binomial multiplicity, total mass, and
Fibonacci moment-collapse consequences for the symmetric softcore replica basis. -/
def pom_replica_softcore_sym_eigenbasis_binomial_weights_statement (q : ℕ) : Prop :=
  (∀ j : ℕ,
    pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_eigenvalue q j =
      (1 - Real.goldenRatio) ^ j * Real.goldenRatio ^ (q - j)) ∧
    (∀ j : ℕ,
      pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_weight q j =
        Nat.choose q j) ∧
    pom_replica_softcore_sym_eigenbasis_binomial_weights_total_mass q = (2 : ℝ) ^ q ∧
    (∀ j : ℕ,
      pom_replica_softcore_sym_eigenbasis_binomial_weights_product_weight q j =
        (Nat.choose q j : ℝ) *
          pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_eigenvalue q j) ∧
    (∀ a b : ℝ,
      (∑ j ∈ Finset.range (q + 1),
          (Nat.choose q j : ℝ) * a ^ (q - j) * b ^ j) = (a + b) ^ q)

/-- Paper label: `prop:pom-replica-softcore-sym-eigenbasis-binomial-weights`. -/
theorem paper_pom_replica_softcore_sym_eigenbasis_binomial_weights (q : ℕ) :
    pom_replica_softcore_sym_eigenbasis_binomial_weights_statement q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    rfl
  · unfold pom_replica_softcore_sym_eigenbasis_binomial_weights_total_mass
      pom_replica_softcore_sym_eigenbasis_binomial_weights_layer_weight
    exact_mod_cast Nat.sum_range_choose q
  · intro j
    rfl
  · intro a b
    rw [add_comm a b, add_pow]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring

end

end Omega.POM
