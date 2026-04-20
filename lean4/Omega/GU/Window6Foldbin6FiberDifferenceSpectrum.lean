import Mathlib.Tactic
import Mathlib.Data.Nat.Dist
import Omega.Folding.BinFold

namespace Omega.GU

private theorem window6_foldbin6_same_fiber_gap_spectrum_fin :
    ∀ a b : Fin 64,
      cBinFold 6 a.1 = cBinFold 6 b.1 →
        Nat.dist a.1 b.1 ∈ ({0, 13, 21, 34, 55} : Finset Nat) := by
  native_decide

/-- Paper-facing same-fiber distance spectrum for `cBinFold` at window `6`.
    lem:window6-foldbin6-fiber-difference-spectrum -/
theorem paper_window6_foldbin6_fiber_difference_spectrum (w : X 6) {a b : Nat} (ha : a < 64)
    (hb : b < 64) (hwa : cBinFold 6 a = w) (hwb : cBinFold 6 b = w) :
    Nat.dist a b ∈ ({0, 13, 21, 34, 55} : Finset Nat) := by
  let a' : Fin 64 := ⟨a, ha⟩
  let b' : Fin 64 := ⟨b, hb⟩
  have hSame : cBinFold 6 a'.1 = cBinFold 6 b'.1 := by
    change cBinFold 6 a = cBinFold 6 b
    rw [hwa, hwb]
  simpa [a', b'] using window6_foldbin6_same_fiber_gap_spectrum_fin a' b' hSame

end Omega.GU
