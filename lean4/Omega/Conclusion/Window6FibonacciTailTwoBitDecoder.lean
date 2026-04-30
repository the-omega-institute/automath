import Mathlib.Tactic
import Omega.Conclusion.Window6FibonacciStaircase

namespace Omega.Conclusion

open Omega

/-- Concrete audit token for the window-`6` Fibonacci tail decoder. -/
abbrev conclusion_window6_fibonacci_tail_two_bit_decoder_data := Unit

namespace conclusion_window6_fibonacci_tail_two_bit_decoder_data

/-- The allowed Fibonacci tail offsets for a window-`6` Zeckendorf rank. -/
def conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets (r : ℕ) : Finset ℕ :=
  if r ≤ 8 then
    ({0, 21, 34, 55} : Finset ℕ)
  else if r ≤ 12 then
    ({0, 21, 34} : Finset ℕ)
  else
    ({0, 34} : Finset ℕ)

/-- Concrete window-`6` tail decoder statement: the three rank bands select the advertised
Fibonacci-offset alphabet and its cardinality matches the folded fiber multiplicity. -/
def conclusion_window6_fibonacci_tail_two_bit_decoder_statement
    (_D : conclusion_window6_fibonacci_tail_two_bit_decoder_data) : Prop :=
  Nat.fib 8 = 21 ∧
    Nat.fib 9 = 34 ∧
    Nat.fib 10 = 55 ∧
    ∀ w : Omega.X 6,
      let r := Omega.stableValue w
      (r ≤ 8 →
          conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r =
              ({0, Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset ℕ) ∧
            Omega.cBinFiberMult 6 w =
              (conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r).card) ∧
        (9 ≤ r ∧ r ≤ 12 →
          conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r =
              ({0, Nat.fib 8, Nat.fib 9} : Finset ℕ) ∧
            Omega.cBinFiberMult 6 w =
              (conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r).card) ∧
        (13 ≤ r ∧ r ≤ 20 →
          conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r =
              ({0, Nat.fib 9} : Finset ℕ) ∧
            Omega.cBinFiberMult 6 w =
              (conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets r).card)

end conclusion_window6_fibonacci_tail_two_bit_decoder_data

open conclusion_window6_fibonacci_tail_two_bit_decoder_data

/-- Paper label: `thm:conclusion-window6-fibonacci-tail-two-bit-decoder`. -/
theorem paper_conclusion_window6_fibonacci_tail_two_bit_decoder
    (D : conclusion_window6_fibonacci_tail_two_bit_decoder_data) :
    D.conclusion_window6_fibonacci_tail_two_bit_decoder_statement := by
  have hf8 : Nat.fib 8 = 21 := by decide
  have hf9 : Nat.fib 9 = 34 := by decide
  have hf10 : Nat.fib 10 = 55 := by decide
  refine ⟨hf8, hf9, hf10, ?_⟩
  intro w
  dsimp
  have hstair := paper_conclusion_window6_fibonacci_staircase w
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    have hmult : Omega.cBinFiberMult 6 w = 4 := hstair.1.mpr hr
    have hoff :
        conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets
            (Omega.stableValue w) =
          ({0, Nat.fib 8, Nat.fib 9, Nat.fib 10} : Finset ℕ) := by
      simp [conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets, hr, hf8, hf9, hf10]
    refine ⟨hoff, ?_⟩
    rw [hmult, hoff]
    norm_num [hf8, hf9, hf10]
  · rintro ⟨hrlow, hrhigh⟩
    have hmult : Omega.cBinFiberMult 6 w = 3 := hstair.2.1.mpr ⟨hrlow, hrhigh⟩
    have hnot_low : ¬ Omega.stableValue w ≤ 8 := by omega
    have hoff :
        conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets
            (Omega.stableValue w) =
          ({0, Nat.fib 8, Nat.fib 9} : Finset ℕ) := by
      simp [conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets, hnot_low, hrhigh,
        hf8, hf9]
    refine ⟨hoff, ?_⟩
    rw [hmult, hoff]
    norm_num [hf8, hf9]
  · rintro ⟨hrlow, hrhigh⟩
    have hmult : Omega.cBinFiberMult 6 w = 2 := hstair.2.2.mpr ⟨hrlow, hrhigh⟩
    have hnot_low : ¬ Omega.stableValue w ≤ 8 := by omega
    have hnot_mid : ¬ Omega.stableValue w ≤ 12 := by omega
    have hoff :
        conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets
            (Omega.stableValue w) =
          ({0, Nat.fib 9} : Finset ℕ) := by
      simp [conclusion_window6_fibonacci_tail_two_bit_decoder_tail_offsets, hnot_low, hnot_mid,
        hf9]
    refine ⟨hoff, ?_⟩
    rw [hmult, hoff]
    norm_num [hf9]

end Omega.Conclusion
