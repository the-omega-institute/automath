import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete CRT readout data: the modulus product `P` and the decision window of radius `bound`. -/
structure CrtOrderReadoutData where
  bound : ℕ
  modulusProduct : ℕ
  modulusProduct_pos : 1 ≤ modulusProduct

namespace CrtOrderReadoutData

/-- Residue-vector readout compressed to the combined modulus `P = ∏ p_i`. On the bounded window
`[-B, B]` this is equivalent to reading residues on the shifted window `{0, …, 2B}`. -/
def residueReadout (D : CrtOrderReadoutData) (i : Fin (2 * D.bound + 1)) : ℕ :=
  i.1 % D.modulusProduct

/-- Every threshold/interval predicate on the bounded window is decidable exactly when the residue
readout is injective there. -/
def canDecideAllThresholds (D : CrtOrderReadoutData) : Prop :=
  Function.Injective D.residueReadout

theorem conclusion_crt_threshold_necessary_sufficient_for_order_readout_forward
    (D : CrtOrderReadoutData) (hprod : 2 * D.bound < D.modulusProduct) :
    D.canDecideAllThresholds := by
  intro i j hij
  apply Fin.ext
  have hi_lt : i.1 < D.modulusProduct := by
    omega
  have hj_lt : j.1 < D.modulusProduct := by
    omega
  simpa [residueReadout, Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] using hij

theorem conclusion_crt_threshold_necessary_sufficient_for_order_readout_reverse
    (D : CrtOrderReadoutData) (hreadout : D.canDecideAllThresholds) :
    2 * D.bound < D.modulusProduct := by
  by_contra hnot
  have hle : D.modulusProduct ≤ 2 * D.bound := Nat.le_of_not_gt hnot
  let i0 : Fin (2 * D.bound + 1) := 0
  let iP : Fin (2 * D.bound + 1) := ⟨D.modulusProduct, by omega⟩
  have hsame : D.residueReadout i0 = D.residueReadout iP := by
    simp [residueReadout, i0, iP]
  have heq : i0 = iP := hreadout hsame
  have hval : (i0 : ℕ) = D.modulusProduct := by
    simpa [i0, iP] using congrArg Fin.val heq
  have hzero : (0 : ℕ) = D.modulusProduct := by
    simpa [i0] using hval
  have hpos : 0 < D.modulusProduct := Nat.succ_le_iff.mp D.modulusProduct_pos
  exact (Nat.ne_of_gt hpos) hzero.symm

end CrtOrderReadoutData

/-- Paper label: `thm:conclusion-crt-threshold-necessary-sufficient-for-order-readout`.
Residue readout on the bounded window is injective exactly when the combined modulus product clears
the sharp CRT threshold `2B`. -/
theorem paper_conclusion_crt_threshold_necessary_sufficient_for_order_readout
    (D : CrtOrderReadoutData) : D.canDecideAllThresholds ↔ 2 * D.bound < D.modulusProduct := by
  constructor
  · exact D.conclusion_crt_threshold_necessary_sufficient_for_order_readout_reverse
  · exact D.conclusion_crt_threshold_necessary_sufficient_for_order_readout_forward

end Omega.Conclusion
