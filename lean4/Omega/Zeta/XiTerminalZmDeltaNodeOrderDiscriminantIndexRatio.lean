import Mathlib.Tactic

namespace Omega.Zeta

/-- The explicit index ratio appearing in the node-order discriminant comparison. -/
def xiTerminalZmDeltaNodeIndexRatio : ℚ :=
  ((2 ^ 7 * 3 * 307 : ℕ) : ℚ) / 31

/-- The prime-by-prime valuation difference read off from the explicit ratio
`2^7 * 3 * 307 / 31`. -/
def xiTerminalZmDeltaNodeLocalValuationDiff (p : ℕ) : ℤ :=
  if p = 2 then 7
  else if p = 3 then 1
  else if p = 307 then 1
  else if p = 31 then -1
  else 0

/-- Concrete data for the comparison of the `y`- and `T`-orders inside the same node field. -/
structure XiTerminalZmDeltaNodeOrderData where
  commonDiscriminant : ℚ
  yIndex : ℕ
  tIndex : ℕ
  yDiscriminant : ℚ
  tDiscriminant : ℚ
  localValuationY : ℕ → ℤ
  localValuationT : ℕ → ℤ
  indexRatio : ℚ
  yIndex_eq : yIndex = 31
  tIndex_eq : tIndex = 2 ^ 7 * 3 * 307
  yDiscriminant_eq : yDiscriminant = commonDiscriminant * (yIndex : ℚ) ^ 2
  tDiscriminant_eq : tDiscriminant = commonDiscriminant * (tIndex : ℚ) ^ 2
  indexRatio_eq : indexRatio = xiTerminalZmDeltaNodeIndexRatio
  localValuationDiff_eq :
    ∀ p,
      localValuationT p - localValuationY p = xiTerminalZmDeltaNodeLocalValuationDiff p

namespace XiTerminalZmDeltaNodeOrderData

/-- The index ratio is the explicit rational number extracted from the two monogenic orders. -/
def hasIndexRatioFormula (h : XiTerminalZmDeltaNodeOrderData) : Prop :=
  h.indexRatio = xiTerminalZmDeltaNodeIndexRatio

/-- The discriminant ratio is the square of the index ratio for the common number field. -/
def hasDiscriminantRatioFormula (h : XiTerminalZmDeltaNodeOrderData) : Prop :=
  h.tDiscriminant = h.yDiscriminant * h.indexRatio ^ 2

/-- Prime-by-prime valuation differences are read off from the explicit index ratio. -/
def hasLocalValuationDiffs (h : XiTerminalZmDeltaNodeOrderData) : Prop :=
  ∀ p,
    h.localValuationT p - h.localValuationY p = xiTerminalZmDeltaNodeLocalValuationDiff p

lemma hasIndexRatioFormula_holds (h : XiTerminalZmDeltaNodeOrderData) : h.hasIndexRatioFormula := by
  exact h.indexRatio_eq

lemma hasDiscriminantRatioFormula_holds (h : XiTerminalZmDeltaNodeOrderData) :
    h.hasDiscriminantRatioFormula := by
  have hy :
      h.yDiscriminant = h.commonDiscriminant * (31 : ℚ) ^ 2 := by
    simpa [h.yIndex_eq] using h.yDiscriminant_eq
  have ht :
      h.tDiscriminant = h.commonDiscriminant * ((2 ^ 7 * 3 * 307 : ℕ) : ℚ) ^ 2 := by
    simpa [h.tIndex_eq] using h.tDiscriminant_eq
  unfold hasDiscriminantRatioFormula
  rw [ht, hy, h.indexRatio_eq]
  rw [xiTerminalZmDeltaNodeIndexRatio]
  field_simp

lemma hasLocalValuationDiffs_holds (h : XiTerminalZmDeltaNodeOrderData) :
    h.hasLocalValuationDiffs := by
  exact h.localValuationDiff_eq

end XiTerminalZmDeltaNodeOrderData

open XiTerminalZmDeltaNodeOrderData

/-- The explicit order-index ratio controls the discriminant ratio and the corresponding local
valuation differences.
    thm:xi-terminal-zm-delta-node-order-discriminant-index-ratio -/
theorem paper_xi_terminal_zm_delta_node_order_discriminant_index_ratio
    (h : XiTerminalZmDeltaNodeOrderData) :
    And h.hasIndexRatioFormula (And h.hasDiscriminantRatioFormula h.hasLocalValuationDiffs) := by
  exact
    ⟨h.hasIndexRatioFormula_holds,
      ⟨h.hasDiscriminantRatioFormula_holds, h.hasLocalValuationDiffs_holds⟩⟩

end Omega.Zeta
