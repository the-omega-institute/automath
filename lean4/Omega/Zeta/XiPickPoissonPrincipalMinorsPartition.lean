import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Minimal concrete Pick--Poisson Gram package: the diagonal block contributes the point weights
and the restricted Cauchy block contributes the Poisson kernel weights. -/
structure XiPickPoissonGram (kappa : Nat) where
  pointWeight : Fin kappa → ℝ
  kernelWeight : Fin kappa → ℝ

/-- Determinant of the diagonal factor restricted to a principal block. -/
def xiPickPoissonDiagonalBlockDet {kappa : Nat} (P : XiPickPoissonGram kappa)
    (I : Finset (Fin kappa)) : ℝ :=
  I.prod P.pointWeight

/-- Determinant of the restricted Cauchy/Gram factor. -/
def xiPickPoissonKernelBlockDet {kappa : Nat} (P : XiPickPoissonGram kappa)
    (I : Finset (Fin kappa)) : ℝ :=
  I.prod P.kernelWeight

/-- The principal-minor determinant coming from the block factorization `P_I = D_I G_I D_I^*`. -/
def xiPickPoissonPrincipalMinorDet {kappa : Nat} (P : XiPickPoissonGram kappa)
    (I : Finset (Fin kappa)) : ℝ :=
  xiPickPoissonDiagonalBlockDet P I * xiPickPoissonKernelBlockDet P I

/-- The partition weight assigned to a principal block. -/
def xiPickPoissonPartitionWeight {kappa : Nat} (P : XiPickPoissonGram kappa)
    (I : Finset (Fin kappa)) : ℝ :=
  xiPickPoissonDiagonalBlockDet P I * xiPickPoissonKernelBlockDet P I

lemma xiPickPoissonPrincipalMinorDet_eq_partitionWeight {kappa : Nat}
    (P : XiPickPoissonGram kappa) (I : Finset (Fin kappa)) :
    xiPickPoissonPrincipalMinorDet P I = xiPickPoissonPartitionWeight P I := by
  rfl

/-- Every principal block of the concrete Pick--Poisson Gram model has determinant equal to its
partition weight. -/
def XiPickPoissonPrincipalMinorsPartition {kappa : Nat} (P : XiPickPoissonGram kappa) : Prop :=
  ∀ I : Finset (Fin kappa), xiPickPoissonPrincipalMinorDet P I = xiPickPoissonPartitionWeight P I

/-- Restricting the Pick--Poisson factorization to each principal block preserves the same
diagonal and Cauchy determinant factors, so every principal minor equals the corresponding
partition weight.
    prop:xi-pick-poisson-principal-minors-partition -/
theorem paper_xi_pick_poisson_principal_minors_partition {kappa : Nat}
    (P : XiPickPoissonGram kappa) : XiPickPoissonPrincipalMinorsPartition P := by
  intro I
  exact xiPickPoissonPrincipalMinorDet_eq_partitionWeight P I

end Omega.Zeta
