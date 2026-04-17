import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete chapter-local data for the unique section of the last-bit-`1` binary minsector map.
The candidate image already has the prefix fixed by the right-inverse condition; the only free
bits are the final two bits `a b`, and the hypotheses `b = 1` and `¬ (a = 1 ∧ b = 1)` force the
unique choice `a = 0`, `b = 1`. -/
structure FoldBinMinsectorLastbit1SectionUniqueData where
  baseWord : List Bool
  middleBit : Bool
  lastBit : Bool
  lastBitIsOne : lastBit = true
  noDoubleOne : ¬ (middleBit = true ∧ lastBit = true)

namespace FoldBinMinsectorLastbit1SectionUniqueData

/-- The explicit section appends the only admissible suffix `01`. -/
def explicitSection (u : List Bool) : List Bool :=
  u ++ [false, true]

/-- The unique right inverse is the candidate word obtained by appending the forced suffix. -/
def uniqueRightInverse (D : FoldBinMinsectorLastbit1SectionUniqueData) : Prop :=
  D.baseWord ++ [D.middleBit, D.lastBit] = explicitSection D.baseWord

/-- The section formula itself is the concrete append-by-`01` rule. -/
def explicitFormula (D : FoldBinMinsectorLastbit1SectionUniqueData) : Prop :=
  explicitSection D.baseWord = D.baseWord ++ [false, true]

end FoldBinMinsectorLastbit1SectionUniqueData

open FoldBinMinsectorLastbit1SectionUniqueData

/-- Paper-facing wrapper for the unique section of the binary minsector map under the last-bit-`1`
constraint.
    prop:fold-bin-minsector-lastbit1-section-unique -/
theorem paper_fold_bin_minsector_lastbit1_section_unique
    (D : FoldBinMinsectorLastbit1SectionUniqueData) :
    D.uniqueRightInverse ∧ D.explicitFormula := by
  have hMiddle : D.middleBit = false := by
    cases hmid : D.middleBit with
    | false =>
        rfl
    | true =>
        exfalso
        exact D.noDoubleOne ⟨hmid, D.lastBitIsOne⟩
  refine ⟨?_, ?_⟩
  · simp [FoldBinMinsectorLastbit1SectionUniqueData.uniqueRightInverse,
      FoldBinMinsectorLastbit1SectionUniqueData.explicitSection, hMiddle, D.lastBitIsOne]
  · rfl

end Omega.Folding
