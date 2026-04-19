import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Fiberwise dimensions of the two same-sheet pair-groupoid blocks. -/
def sameSheetDimension (a b : ℤ) : ℤ := a ^ 2 + b ^ 2

/-- Dimension of the ambient full pair-groupoid block after forgetting the hidden bit. -/
def totalSheetDimension (a b : ℤ) : ℤ := (a + b) ^ 2

/-- The excess index created by merging the two hidden sheets. -/
def hiddenbitIndex (a b : ℤ) : ℤ := totalSheetDimension a b - sameSheetDimension a b

/-- The same-sheet subgroupoid splits as the sum of the two pair-groupoid blocks. -/
def hiddenbitSheetBlockDecomposition (a b : ℤ) : Prop :=
  sameSheetDimension a b = a ^ 2 + b ^ 2

/-- The block-diagonal algebra embeds into the merged ambient block. -/
def hiddenbitBlockDiagonalEmbedding (a b : ℤ) : Prop :=
  sameSheetDimension a b ≤ totalSheetDimension a b

/-- The index is the off-diagonal contribution `2ab`. -/
def hiddenbitIndexFormula (a b : ℤ) : Prop := hiddenbitIndex a b = 2 * a * b

/-- The merged block lies between the same-sheet block and twice its size. -/
def hiddenbitIndexBounds (a b : ℤ) : Prop :=
  sameSheetDimension a b ≤ totalSheetDimension a b ∧
    totalSheetDimension a b ≤ 2 * sameSheetDimension a b

/-- The upper bound is sharp exactly when the two sheets have the same size. -/
def hiddenbitUpperBoundEqIffBalanced (a b : ℤ) : Prop :=
  totalSheetDimension a b = 2 * sameSheetDimension a b ↔ a = b

/-- Paper-facing wrapper for the hidden-sheet subgroupoid index estimate.
    prop:op-algebra-hiddenbit-sheet-subgroupoid-index -/
theorem paper_op_algebra_hiddenbit_sheet_subgroupoid_index
    (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    hiddenbitSheetBlockDecomposition a b ∧
      hiddenbitBlockDiagonalEmbedding a b ∧
      hiddenbitIndexFormula a b ∧
      hiddenbitIndexBounds a b ∧
      hiddenbitUpperBoundEqIffBalanced a b := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · dsimp [hiddenbitBlockDiagonalEmbedding, sameSheetDimension, totalSheetDimension]
    nlinarith
  · dsimp [hiddenbitIndexFormula, hiddenbitIndex, sameSheetDimension, totalSheetDimension]
    ring
  · constructor
    · dsimp [hiddenbitIndexBounds, sameSheetDimension, totalSheetDimension]
      nlinarith
    · dsimp [hiddenbitIndexBounds, sameSheetDimension, totalSheetDimension]
      have hsq : 0 ≤ (a - b) ^ 2 := by nlinarith
      nlinarith
  · constructor
    · intro h
      dsimp [hiddenbitUpperBoundEqIffBalanced, sameSheetDimension, totalSheetDimension] at h
      have hsq : 0 ≤ (a - b) ^ 2 := by nlinarith
      nlinarith
    · intro h
      subst h
      dsimp [hiddenbitUpperBoundEqIffBalanced, sameSheetDimension, totalSheetDimension]
      ring

end Omega.OperatorAlgebra
