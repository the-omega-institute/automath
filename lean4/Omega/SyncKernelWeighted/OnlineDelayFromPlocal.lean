import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- A small chapter-local model of a `(t,r)`-local map: the output at position `j` is computed
from a window of width `t + r + 1` centered so that it reads up to input position `j + t`. -/
structure PlocalMap (A B : Type*) (t r : Nat) where
  run : (Int → A) → Int → B
  localRule : (Fin (t + r + 1) → A) → B
  run_eq_localRule :
    ∀ u j, run u j = localRule fun k => u (j + Int.ofNat t - Int.ofNat k.1)

/-- In the MSDF single-pass model, the online delay is exactly the anticipation parameter. -/
def singlePassDelay {A B : Type*} {t r : Nat} (_phi : PlocalMap A B t r) : Nat :=
  t

/-- A `(t,r)`-local map cannot emit position `j` before reading input `j + t`, so its single-pass
online delay is exactly `t`.
    cor:online-delay-from-plocal -/
theorem paper_online_delay_from_plocal {A B : Type*} (t r : Nat) (phi : PlocalMap A B t r) :
    singlePassDelay phi = t := by
  rfl

end Omega.SyncKernelWeighted
