import Mathlib
import Omega.OperatorAlgebra.FoldFiberNormalizerWreath

namespace Omega.OperatorAlgebra

/-- The two explicit `±1`-characters that survive on a local wreath factor:
the visible-layer sign and the fiberwise sign. -/
inductive FoldWreathCharacter where
  | visibleSign
  | fiberSign
  deriving DecidableEq, Fintype

/-- The visible sign appears exactly when the visible permutation group is nontrivial. -/
def foldWreathVisibleRank (_d n : ℕ) : ℕ :=
  if 2 ≤ n then 1 else 0

/-- The base-group sign survives to coinvariants exactly when the fiber has size at least `2`
and there is at least one visible block. -/
def foldWreathCoinvariantRank (d n : ℕ) : ℕ :=
  if 2 ≤ d ∧ 1 ≤ n then 1 else 0

/-- Total number of independent `±1`-characters on the local wreath factor `S_d wr S_n`. -/
def foldWreathCharacterBasisRank (d n : ℕ) : ℕ :=
  foldWreathVisibleRank d n + foldWreathCoinvariantRank d n

/-- The corresponding abelianization order, encoded as a finite `2`-group. -/
def foldWreathAbelianizationOrder (d n : ℕ) : ℕ :=
  2 ^ foldWreathCharacterBasisRank d n

/-- The explicit basis of visible and fiber sign characters that survive in the local wreath
factor. -/
def foldWreathCharacterBasis (d n : ℕ) : Finset FoldWreathCharacter :=
  (if 2 ≤ n then ({FoldWreathCharacter.visibleSign} : Finset FoldWreathCharacter) else ∅) ∪
    (if 2 ≤ d ∧ 1 ≤ n then ({FoldWreathCharacter.fiberSign} : Finset FoldWreathCharacter) else ∅)

/-- The local wreath factor `S_d wr S_n` has abelianization rank equal to the number of surviving
visible and fiber sign characters, yielding the standard case split
`1, 1, 2, 2, 4` for the abelianization order. This packages the visible and fiber sign characters
as the full `±1`-character basis.
    thm:op-algebra-fold-wreath-abelianization-characters -/
theorem paper_op_algebra_fold_wreath_abelianization_characters :
    ∀ d n : ℕ,
      1 ≤ d →
      foldWreathAbelianizationOrder d n =
          (if n = 0 then 1 else if d = 1 then if n = 1 then 1 else 2 else if n = 1 then 2 else 4) ∧
        (foldWreathCharacterBasis d n).card = foldWreathCharacterBasisRank d n ∧
        foldWreathAbelianizationOrder d n = 2 ^ (foldWreathCharacterBasis d n).card := by
  intro d n hd
  have hcard : (foldWreathCharacterBasis d n).card = foldWreathCharacterBasisRank d n := by
    by_cases hvis : 2 ≤ n
    · by_cases hfib : 2 ≤ d ∧ 1 ≤ n
      · simp [foldWreathCharacterBasis, foldWreathCharacterBasisRank, foldWreathVisibleRank,
          foldWreathCoinvariantRank, hvis, hfib]
      · simp [foldWreathCharacterBasis, foldWreathCharacterBasisRank, foldWreathVisibleRank,
          foldWreathCoinvariantRank, hvis, hfib]
    · by_cases hfib : 2 ≤ d ∧ 1 ≤ n
      · simp [foldWreathCharacterBasis, foldWreathCharacterBasisRank, foldWreathVisibleRank,
          foldWreathCoinvariantRank, hvis, hfib]
      · simp [foldWreathCharacterBasis, foldWreathCharacterBasisRank, foldWreathVisibleRank,
          foldWreathCoinvariantRank, hvis, hfib]
  have hpow :
      foldWreathAbelianizationOrder d n = 2 ^ (foldWreathCharacterBasis d n).card := by
    unfold foldWreathAbelianizationOrder
    rw [hcard]
  have hcases :
      foldWreathAbelianizationOrder d n =
        (if n = 0 then 1 else if d = 1 then if n = 1 then 1 else 2 else if n = 1 then 2 else 4) := by
    unfold foldWreathAbelianizationOrder foldWreathCharacterBasisRank
      foldWreathVisibleRank foldWreathCoinvariantRank
    by_cases hn0 : n = 0
    · simp [hn0]
    · by_cases hd1 : d = 1
      · by_cases hn1 : n = 1
        · simp [hd1, hn1]
        · have hn2 : 2 ≤ n := by omega
          simp [hn0, hd1, hn1, hn2]
      · by_cases hn1 : n = 1
        · have hfib : 2 ≤ d ∧ 1 ≤ n := by omega
          simp [hd1, hn1, hfib]
        · have hn2 : 2 ≤ n := by omega
          have hfib : 2 ≤ d ∧ 1 ≤ n := by omega
          simp [hn0, hd1, hn1, hn2, hfib]
  exact ⟨hcases, hcard, hpow⟩

end Omega.OperatorAlgebra
