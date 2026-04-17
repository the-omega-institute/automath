import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GU

/-- The boundary sector picks out the three dyadic directions in descending support size. -/
def boundaryDirectionMask : Nat → Nat
  | 0 => 62
  | 1 => 38
  | _ => 34

/-- Support of a six-bit mask, read in least-significant-bit order. -/
def support (mask : Nat) : Finset Nat :=
  (Finset.range 6).filter fun i => Nat.testBit mask i

/-- XOR value of a finite mask family. -/
def xorValue (masks : List Nat) : Nat :=
  masks.foldl Nat.xor 0

/-- `xorIndependent` means every nonempty subfamily has nonzero XOR sum. -/
def xorIndependent (masks : List Nat) : Prop :=
  ∀ ys ∈ masks.sublists, ys ≠ [] → xorValue ys ≠ 0

instance instDecidableXorIndependent (masks : List Nat) : Decidable (xorIndependent masks) := by
  unfold xorIndependent
  infer_instance

/-- The window-6 boundary directions are exactly `62`, `38`, `34`, with nested supports and
nontrivial `F₂`-independence under XOR. -/
theorem paper_window6_boundary_dyadic_direction_flag :
    boundaryDirectionMask 0 = 62 ∧
      boundaryDirectionMask 1 = 38 ∧
      boundaryDirectionMask 2 = 34 ∧
      support (boundaryDirectionMask 2) ⊂ support (boundaryDirectionMask 1) ∧
      support (boundaryDirectionMask 1) ⊂ support (boundaryDirectionMask 0) ∧
      xorIndependent
        [boundaryDirectionMask 0, boundaryDirectionMask 1, boundaryDirectionMask 2] := by
  native_decide

end Omega.GU
