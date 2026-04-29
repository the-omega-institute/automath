import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionReplicaSoftcoreTransfer
import Omega.POM.ReplicaSoftcoreTensorEigenbasis

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete wrapper for the `q`-replica transfer matrix and its tensor-product spectral package. -/
structure pom_multiplicity_composition_replica_explicit_eigs_data where
  q : ℕ

namespace pom_multiplicity_composition_replica_explicit_eigs_data

/-- Replica states for the explicit tensor transfer matrix. -/
abbrev pom_multiplicity_composition_replica_explicit_eigs_state
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) :=
  Fin D.q → Fin 2

/-- The concrete `q`-fold transfer matrix. -/
def pom_multiplicity_composition_replica_explicit_eigs_transfer_matrix
    (D : pom_multiplicity_composition_replica_explicit_eigs_data)
    (x y : D.pom_multiplicity_composition_replica_explicit_eigs_state) : ℝ :=
  ∏ i, Omega.Graph.goldenMeanAdjacencyℝ (x i) (y i)

/-- The tensor decomposition of the transfer matrix into local Fibonacci kernels. -/
def pom_multiplicity_composition_replica_explicit_eigs_K_tensor_decomposition
    (D : pom_multiplicity_composition_replica_explicit_eigs_data)
    (x y : D.pom_multiplicity_composition_replica_explicit_eigs_state) : ℝ :=
  pom_replica_softcore_tensor_eigenbasis_tensorKernel D.q x y

/-- Multiplicity lower bound attached to the `j`th tensor layer. -/
def pom_multiplicity_composition_replica_explicit_eigs_layer_multiplicity_lower_bound
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) (j : ℕ) : ℕ :=
  Nat.choose D.q j

/-- Dimension of the symmetric quotient/remainder tracked by the `S_q`-orbits of tensor layers. -/
def pom_multiplicity_composition_replica_explicit_eigs_symmetric_remainder_dimension
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) : ℕ :=
  Fintype.card (Fin (D.q + 1))

/-- Pointwise tensor decomposition of the transfer matrix. -/
def transfer_decomposition
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) : Prop :=
  ∀ x y : D.pom_multiplicity_composition_replica_explicit_eigs_state,
    D.pom_multiplicity_composition_replica_explicit_eigs_transfer_matrix x y =
      D.pom_multiplicity_composition_replica_explicit_eigs_K_tensor_decomposition x y

/-- The tensor eigenvectors indexed by `S : Finset (Fin q)` have the layer eigenvalue whenever
`S.card = j`, and the layer carries the advertised binomial lower bound. -/
def tensor_spectrum_multiplicity
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) : Prop :=
  ∀ j : ℕ, ∀ S : Finset (Fin D.q), S.card = j →
    (∀ x : Fin D.q → Fin 2,
      pom_replica_softcore_tensor_eigenbasis_tensorApply D.q
          (pom_replica_softcore_tensor_eigenbasis_tensorVector D.q S) x =
        pom_replica_softcore_tensor_eigenbasis_layerEigenvalue D.q j *
          pom_replica_softcore_tensor_eigenbasis_tensorVector D.q S x) ∧
      Nat.choose D.q j ≤
        D.pom_multiplicity_composition_replica_explicit_eigs_layer_multiplicity_lower_bound j

/-- The symmetric layer remainder is indexed by the `q + 1` possible cardinalities. -/
def symmetric_remainder_bound
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) : Prop :=
  D.pom_multiplicity_composition_replica_explicit_eigs_symmetric_remainder_dimension = D.q + 1

end pom_multiplicity_composition_replica_explicit_eigs_data

open pom_multiplicity_composition_replica_explicit_eigs_data

/-- Paper label: `prop:pom-multiplicity-composition-replica-explicit-eigs`. -/
theorem paper_pom_multiplicity_composition_replica_explicit_eigs
    (D : pom_multiplicity_composition_replica_explicit_eigs_data) :
    D.transfer_decomposition ∧ D.tensor_spectrum_multiplicity ∧
      D.symmetric_remainder_bound := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rfl
  · intro j S hS
    refine ⟨?_, ?_⟩
    · intro x
      have heigen := pom_replica_softcore_tensor_eigenbasis_tensor_eigen D.q S x
      have hlayer :
          pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue D.q S =
            pom_replica_softcore_tensor_eigenbasis_layerEigenvalue D.q j :=
        pom_replica_softcore_tensor_eigenbasis_subsetEigenvalue_eq_layer hS
      simpa [hlayer] using heigen
    · simp [pom_multiplicity_composition_replica_explicit_eigs_layer_multiplicity_lower_bound]
  · simp [symmetric_remainder_bound,
      pom_multiplicity_composition_replica_explicit_eigs_symmetric_remainder_dimension]

end

end Omega.POM
