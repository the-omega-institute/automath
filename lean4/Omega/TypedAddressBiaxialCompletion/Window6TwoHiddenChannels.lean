import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.TypedAddressBiaxialCompletion

/-- The two visible hidden channels at window 6 are the universal `F₉ = 34` sheet-parity offset and
the optional `F₈ = 21` repair offset; the `F₁₀ = 55` offset appears only on the four-sheet fibers.
-/
def window6HiddenOffsets (w : X 6) : Finset Nat :=
  match cBinFiberMult 6 w with
  | 2 => {0, 34}
  | 3 => {0, 21, 34}
  | 4 => {0, 21, 34, 55}
  | _ => {34}

private lemma cBinFiberMult_six_ge_two (w : X 6) : 2 ≤ cBinFiberMult 6 w := by
  have hmin : cBinFiberMin 6 ≤ cBinFiberMult 6 w := by
    simpa [cBinFiberMin] using
      (Finset.inf'_le (s := (Finset.univ : Finset (X 6))) (f := fun x => cBinFiberMult 6 x)
        (by simp : w ∈ (Finset.univ : Finset (X 6))))
  rwa [cBinFiberMin_six] at hmin

theorem paper_typed_address_biaxial_completion_window6_two_hidden_channels :
    (∀ w : X 6, 21 ∈ window6HiddenOffsets w ↔ 3 ≤ cBinFiberMult 6 w) ∧
      (∀ w : X 6, 34 ∈ window6HiddenOffsets w) ∧
      (∀ w : X 6, cBinFiberMult 6 w = 2 → window6HiddenOffsets w = ({0, 34} : Finset Nat)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have hlo := cBinFiberMult_six_ge_two w
    have hhi := conclusion_window6_su5_obstruction w
    interval_cases hmult : cBinFiberMult 6 w <;> simp [window6HiddenOffsets, hmult]
  · intro w
    have hlo := cBinFiberMult_six_ge_two w
    have hhi := conclusion_window6_su5_obstruction w
    interval_cases hmult : cBinFiberMult 6 w <;> simp [window6HiddenOffsets, hmult]
  · intro w hw
    simp [window6HiddenOffsets, hw]

end Omega.TypedAddressBiaxialCompletion
