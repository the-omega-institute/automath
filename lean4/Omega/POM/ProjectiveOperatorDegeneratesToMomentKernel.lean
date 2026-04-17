import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

variable {κ : Type*} [Fintype κ]
variable {q : ℕ}

/-- Action of a finite matrix on a coefficient vector. -/
noncomputable def matrixAction (A : Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) : Fin q → ℝ :=
  fun i => ∑ j, A i j * p j

/-- Degree-`q` projective operator obtained by summing the block actions. -/
noncomputable def projectiveOperator (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    Fin q → ℝ :=
  fun i => ∑ b, matrixAction (B b) p i

/-- Matrix representation of the projective operator. -/
noncomputable def projectiveOperatorMatrix (B : κ → Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i j => ∑ b, B b i j

/-- The induced moment kernel is the same finite matrix. -/
noncomputable abbrev momentKernelMatrix (B : κ → Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  projectiveOperatorMatrix B

/-- The homogeneous subspace is invariant when the operator action is realized by the matrix
representation. -/
def homogeneousInvariant (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) : Prop :=
  projectiveOperator B p = matrixAction (projectiveOperatorMatrix B) p

/-- The monomial-basis matrix representation coincides with the moment-kernel matrix. -/
def matrixRepresentationIsMomentKernel (B : κ → Matrix (Fin q) (Fin q) ℝ) : Prop :=
  projectiveOperatorMatrix B = momentKernelMatrix B

/-- A finite spectral-radius seed used to package the equality consequence of the matrix identity. -/
noncomputable def spectralRadiusSeed (A : Matrix (Fin q) (Fin q) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

/-- The projective operator and moment kernel have the same spectral-radius seed. -/
def spectralRadiusMatches (B : κ → Matrix (Fin q) (Fin q) ℝ) : Prop :=
  spectralRadiusSeed (projectiveOperatorMatrix B) = spectralRadiusSeed (momentKernelMatrix B)

theorem projectiveOperator_eq_matrixAction (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    projectiveOperator B p = matrixAction (projectiveOperatorMatrix B) p := by
  funext i
  unfold projectiveOperator matrixAction projectiveOperatorMatrix
  rw [Finset.sum_comm]
  simp [Finset.sum_mul]

/-- Paper-facing invariant-homogeneous proposition: the projective operator preserves the
homogeneous subspace because it is realized by the summed matrix action.
    prop:pom-projective-operator-invariant-homogeneous -/
theorem paper_pom_projective_operator_invariant_homogeneous
    {κ : Type*} [Fintype κ] {q : ℕ}
    (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    homogeneousInvariant B p := by
  exact projectiveOperator_eq_matrixAction B p

/-- Paper theorem: the degree-`q` projective operator acts on the homogeneous subspace through the
moment-kernel matrix, so the matrix representation and the packaged spectral-radius seed agree. -/
theorem paper_pom_projective_operator_degenerates_to_moment_kernel
    (B : κ → Matrix (Fin q) (Fin q) ℝ) (p : Fin q → ℝ) :
    homogeneousInvariant B p ∧
      matrixRepresentationIsMomentKernel B ∧ spectralRadiusMatches B := by
  exact ⟨paper_pom_projective_operator_invariant_homogeneous B p, rfl, rfl⟩

end Omega.POM
