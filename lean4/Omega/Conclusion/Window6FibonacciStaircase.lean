import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.FiberArithmetic

/-- Window-`6` finite audit by stable value. -/
private theorem conclusion_window6_fibonacci_staircase_value_audit (n : Fin 21) :
    (Omega.cBinFiberMult 6 (Omega.X.ofNat 6 n.val) = 4 ↔ n.val ≤ 8) ∧
      (Omega.cBinFiberMult 6 (Omega.X.ofNat 6 n.val) = 3 ↔ 9 ≤ n.val ∧ n.val ≤ 12) ∧
        (Omega.cBinFiberMult 6 (Omega.X.ofNat 6 n.val) = 2 ↔ 13 ≤ n.val ∧ n.val ≤ 20) := by
  fin_cases n <;> native_decide

/-- Paper label: `thm:conclusion-window6-fibonacci-staircase`. -/
theorem paper_conclusion_window6_fibonacci_staircase :
    (∀ w : Omega.X 6,
      (Omega.cBinFiberMult 6 w = 4 ↔ Omega.stableValue w ≤ 8) ∧
        (Omega.cBinFiberMult 6 w = 3 ↔
          9 ≤ Omega.stableValue w ∧ Omega.stableValue w ≤ 12) ∧
          (Omega.cBinFiberMult 6 w = 2 ↔
            13 ≤ Omega.stableValue w ∧ Omega.stableValue w ≤ 20)) := by
  intro w
  let n : Fin 21 := ⟨Omega.stableValue w, by
    have hlt := Omega.stableValue_lt_fib w
    have hfib : Nat.fib (6 + 2) = 21 := by native_decide
    simpa [hfib] using hlt⟩
  have hw : w = Omega.X.ofNat 6 n.val := by
    apply Omega.X.eq_of_stableValue_eq
    have hnlt : n.val < Nat.fib (6 + 2) := by
      have hlt : n.val < 21 := n.isLt
      have hfib : Nat.fib (6 + 2) = 21 := by native_decide
      rw [hfib]
      exact hlt
    rw [Omega.X.stableValue_ofNat_lt n.val hnlt]
  have hnlt : n.val < Nat.fib (6 + 2) := by
    have hlt : n.val < 21 := n.isLt
    have hfib : Nat.fib (6 + 2) = 21 := by native_decide
    rw [hfib]
    exact hlt
  have hstable : Omega.stableValue (Omega.X.ofNat 6 n.val) = n.val :=
    Omega.X.stableValue_ofNat_lt n.val hnlt
  rw [hw]
  simpa [hstable] using conclusion_window6_fibonacci_staircase_value_audit n
