import Omega.Folding.FiberSpectrum

/-! ### Boundary layer counting

A stable word x ∈ X_m is a boundary element if both its first and last bits
are true: x[0] = true ∧ x[m-1] = true. The boundary count b(m) tracks how
many stable words lie in this "boundary layer". -/

namespace Omega

/-- The boundary count: number of stable words with both endpoints true.
    For m ≤ 1 this is vacuously 0 or trivial. -/
def cBoundaryCount : (m : Nat) → Nat
  | 0 => 0
  | 1 => (@Finset.univ (X 1) (fintypeX 1)).filter
      (fun x => x.1 ⟨0, by omega⟩ = true) |>.card
  | m + 2 => (@Finset.univ (X (m + 2)) (fintypeX (m + 2))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true ∧ x.1 ⟨m + 1, by omega⟩ = true) |>.card

/-- Boundary count base values via native_decide. -/
theorem cBoundaryCount_three : cBoundaryCount 3 = 1 := by native_decide
theorem cBoundaryCount_four : cBoundaryCount 4 = 1 := by native_decide
theorem cBoundaryCount_five : cBoundaryCount 5 = 2 := by native_decide
/-- cor:bdry-m6-square-instance -/
theorem cBoundaryCount_six : cBoundaryCount 6 = 3 := by native_decide
theorem cBoundaryCount_seven : cBoundaryCount 7 = 5 := by native_decide
theorem cBoundaryCount_eight : cBoundaryCount 8 = 8 := by native_decide

/-- The boundary count follows a Fibonacci pattern: b(m) = F(m-2) for m = 3..8.
    b(3)=1=F(1), b(4)=1=F(2), b(5)=2=F(3), b(6)=3=F(4), b(7)=5=F(5), b(8)=8=F(6).
    prop:bdry-fib-square-identity -/
theorem cBoundaryCount_eq_fib (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 8) :
    cBoundaryCount m = Nat.fib (m - 2) := by
  interval_cases m <;> native_decide

/-- The boundary gap: |X_m| - b(m) for the verified range.
    gap(6) = 21 - 3 = 18, gap(7) = 34 - 5 = 29, gap(8) = 55 - 8 = 47. -/
theorem boundary_gap_six : Fintype.card (X 6) - cBoundaryCount 6 = 18 := by
  rw [X.card_eq_fib, cBoundaryCount_six]; native_decide
theorem boundary_gap_seven : Fintype.card (X 7) - cBoundaryCount 7 = 29 := by
  rw [X.card_eq_fib, cBoundaryCount_seven]; native_decide
theorem boundary_gap_eight : Fintype.card (X 8) - cBoundaryCount 8 = 47 := by
  rw [X.card_eq_fib, cBoundaryCount_eight]; native_decide

/-- Fibonacci arithmetic: F(9) - F(2) = 34 - 1 = 33. -/
theorem boundary_gap_33_value : Nat.fib 9 - Nat.fib 2 = 33 := by native_decide

/-- The count of stable words with first bit true. -/
def cFirstBitTrueCount : (m : Nat) → Nat
  | 0 => 0
  | m + 1 => (@Finset.univ (X (m + 1)) (fintypeX (m + 1))).filter
      (fun x => x.1 ⟨0, by omega⟩ = true) |>.card

/-- First-bit-true count base values. -/
theorem cFirstBitTrueCount_three : cFirstBitTrueCount 3 = 2 := by native_decide
theorem cFirstBitTrueCount_four : cFirstBitTrueCount 4 = 3 := by native_decide
theorem cFirstBitTrueCount_five : cFirstBitTrueCount 5 = 5 := by native_decide
theorem cFirstBitTrueCount_six : cFirstBitTrueCount 6 = 8 := by native_decide
theorem cFirstBitTrueCount_seven : cFirstBitTrueCount 7 = 13 := by native_decide

/-- The first-bit-true count equals F(m): #{x ∈ X_m : x[0]=true} = F(m) for m=3..7. -/
theorem cFirstBitTrueCount_eq_fib (m : Nat) (hm1 : 3 ≤ m) (hm : m ≤ 7) :
    cFirstBitTrueCount m = Nat.fib m := by
  interval_cases m <;> native_decide

end Omega
