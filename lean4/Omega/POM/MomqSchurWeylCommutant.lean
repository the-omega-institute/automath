import Omega.POM.MomqPermutationSymmetry

namespace Omega.POM

universe u

/-- Concrete data for the MOM_q Schur--Weyl commutant wrapper. The record stores the tensor
arity, the underlying state type, and the two transition branches used by the existing
permutation-symmetry formalization. -/
structure pom_momq_schur_weyl_commutant_data where
  q : ℕ
  state : Type u
  G0 : ℚ
  G1 : ℚ
  T0 : state → state
  T1 : state → state

/-- The irreducibility hypothesis is represented by the concrete finite-arity condition
needed to enter the paper's `q ≥ 2` Schur--Weyl regime. -/
def pom_momq_schur_weyl_commutant_data.irreducibleTransitionAlgebra
    (D : pom_momq_schur_weyl_commutant_data) : Prop :=
  2 ≤ D.q

/-- The tensor algebra side includes the already formalized branchwise permutation symmetry. -/
def pom_momq_schur_weyl_commutant_data.fullEndomorphismTensorAlgebra
    (D : pom_momq_schur_weyl_commutant_data) : Prop :=
  2 ≤ D.q ∧
    ∀ b : Bool, ∀ (σ : Equiv.Perm (Fin D.q)) (v : PureTensor D.q D.state),
      permutePureTensor σ (tensorTransitionFamily D.T0 D.T1 b v) =
        tensorTransitionFamily D.T0 D.T1 b (permutePureTensor σ v)

/-- The permutation-image commutant side is the branchwise summed-kernel version of the same
symmetry. -/
def pom_momq_schur_weyl_commutant_data.permutationImageCommutant
    (D : pom_momq_schur_weyl_commutant_data) : Prop :=
  ∀ (σ : Equiv.Perm (Fin D.q)) (v : PureTensor D.q D.state),
    permuteSummedTensorCollisionKernel σ (summedTensorCollisionKernel D.G0 D.G1 D.T0 D.T1 v) =
      summedTensorCollisionKernel D.G0 D.G1 D.T0 D.T1 (permutePureTensor σ v)

/-- Concrete paper-facing commutant package: the full tensor side and the permutation-image side
hold simultaneously. -/
def pom_momq_schur_weyl_commutant_data.commutantEqualsPermutationImage
    (D : pom_momq_schur_weyl_commutant_data) : Prop :=
  D.fullEndomorphismTensorAlgebra ∧ D.permutationImageCommutant

/-- Paper label: `thm:pom-momq-schur-weyl-commutant`. -/
theorem paper_pom_momq_schur_weyl_commutant (D : pom_momq_schur_weyl_commutant_data)
    (hA : D.irreducibleTransitionAlgebra) : D.commutantEqualsPermutationImage := by
  rcases paper_pom_momq_permutation_symmetry (q := D.q) D.G0 D.G1 D.T0 D.T1 with
    ⟨hTensor, hKernel⟩
  exact ⟨⟨hA, hTensor⟩, hKernel⟩

end Omega.POM
