import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

/-- Paper witness for the failure of strong lumpability at window 6: the microstates
`0 = 000000₂` and `21 = 010101₂ = F₈` lie in the same BinFold fiber, but their one-step
neighbor counts toward some folded type differ.
    prop:terminal-foldbin6-strong-lumpability-fails -/
theorem paper_terminal_foldbin6_strong_lumpability_fails :
    cBinFold 6 0 = cBinFold 6 21 ∧
      ∃ y : X 6,
        ((Finset.range 6).filter (fun k => cBinFold 6 (0 ^^^ (2 ^ k)) = y)).card ≠
          ((Finset.range 6).filter (fun k => cBinFold 6 (21 ^^^ (2 ^ k)) = y)).card := by
  refine ⟨by native_decide, ?_⟩
  refine ⟨X.ofNat 6 1, ?_⟩
  native_decide

end Omega.GU
