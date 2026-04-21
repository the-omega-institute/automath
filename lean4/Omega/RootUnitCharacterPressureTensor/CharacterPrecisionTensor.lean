import Mathlib.Tactic
import Omega.RootUnitCharacterPressureTensor.RootUnitCharacterDiagonalization

namespace Omega.RootUnitCharacterPressureTensor

/-- The depth direction appearing in the tensorized precision channel. -/
abbrev DepthProfile := ℕ → ℂ

/-- Tensor product of a depth profile with a finite character vector. -/
abbrev CharacterPrecisionTensorSpace (q : ℕ) := ℕ → RootUnitOrbitModule q

/-- Translation by logarithmic depth `m`. -/
def depthTranslationChannel (m : ℕ) (g : DepthProfile) : DepthProfile :=
  fun n => g (n + m)

/-- Simple tensors in the depth-character product model. -/
def depthCharacterTensor {q : ℕ} (g : DepthProfile) (F : RootUnitOrbitModule q) :
    CharacterPrecisionTensorSpace q := fun n => g n • F

/-- The joint tensor operator acts by the finite character dilation on each depth slice. -/
noncomputable def characterPrecisionTensorOperator (σ q : ℕ)
    (H : CharacterPrecisionTensorSpace q) : CharacterPrecisionTensorSpace q :=
  fun n => rootUnitWittDilation σ q (H n)

/-- Direct-sum decomposition of the tensor operator into scalar-weighted character blocks. -/
def characterPrecisionTensorDecomposes (σ q : ℕ) : Prop :=
  ∀ H : CharacterPrecisionTensorSpace q,
    characterPrecisionTensorOperator σ q H =
      fun n => ∑ χ : Fin q,
        (H n χ) • (rootUnitDirichletLSeries σ q χ • rootUnitCharacterEigenvector q χ)

/-- Zero-frequency eigenvalue obtained by evaluating the constant-depth character tensor at depth
`0` and the matching character coordinate. -/
noncomputable def characterPrecisionZeroFrequencyEigenvalue (σ q : ℕ) (χ : Fin q) : ℂ :=
  characterPrecisionTensorOperator σ q
      (depthCharacterTensor (fun _ => (1 : ℂ)) (rootUnitCharacterEigenvector q χ)) 0 χ

/-- Paper label: `thm:character-precision-tensor`. The finite character factor diagonalizes the
tensor operator into character blocks, and the zero-frequency eigenvalue on each block is the
corresponding finite Dirichlet `L`-series scalar. -/
theorem paper_character_precision_tensor (σ q : ℕ) :
    characterPrecisionTensorDecomposes σ q ∧
      ∀ χ, characterPrecisionZeroFrequencyEigenvalue σ q χ = rootUnitDirichletLSeries σ q χ := by
  refine ⟨?_, ?_⟩
  · intro H
    ext n a
    have hdecomp := congrArg (fun F : RootUnitOrbitModule q => F a)
      (rootUnitCharacter_direct_sum q (fun χ => H n χ * rootUnitDirichletLSeries σ q χ))
    simpa [characterPrecisionTensorOperator, rootUnitWittDilation, rootUnitCharacterEigenvector,
      smul_smul, mul_comm, mul_left_comm] using hdecomp.symm
  · intro χ
    have hχ := congrArg (fun F : RootUnitOrbitModule q => F χ) (rootUnitWittDilation_eigenvector σ q χ)
    simpa [characterPrecisionZeroFrequencyEigenvalue, characterPrecisionTensorOperator,
      depthCharacterTensor, rootUnitCharacterEigenvector, mul_comm, mul_left_comm, mul_assoc] using hχ

end Omega.RootUnitCharacterPressureTensor
