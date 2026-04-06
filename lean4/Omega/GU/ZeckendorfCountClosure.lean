import Omega.Folding.StableSyntax
import Omega.Folding.FiberArithmetic
import Omega.Folding.FiberArithmeticProperties
import Mathlib.Tactic

open Omega X

namespace Omega.GU

/-- cor:su5-21-plus-3-closure -/
theorem su5_count_closure_X6_X2 :
    24 = Fintype.card (X 6) + Fintype.card (X 2) := by
  rw [X.card_X_six, X.card_X_two]

/-- cor:su5-21-plus-3-closure -/
theorem su5_count_closure_fib :
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 4 = Fintype.card (X 2) ∧
    24 = Fintype.card (X 6) + Fintype.card (X 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [X.card_eq_fib]
  · rw [X.card_eq_fib]
  · rw [X.card_X_six, X.card_X_two]

/-- The three tail offsets {F_8, F_9, F_10} = {21, 34, 55}.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_tail_offsets :
    Nat.fib 8 = 21 ∧ Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- GUT top-term Fibonacci alignment: SU(5)/SO(10)/E_6.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem gut_top_fibonacci_terms :
    (24 = Nat.fib 8 + Nat.fib 4) ∧
    (45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4) ∧
    (78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Tail offsets = |X_6|, |X_7|, |X_8|.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_tail_offsets_are_card_X :
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 9 = Fintype.card (X 7) ∧
    Nat.fib 10 = Fintype.card (X 8) := by
  exact ⟨(X.card_eq_fib 6).symm, (X.card_eq_fib 7).symm, (X.card_eq_fib 8).symm⟩

/-- The resonance gap: |X_8| - |X_6| = |X_7|.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem fold6_resonance_gap :
    Fintype.card (X 8) - Fintype.card (X 6) = Fintype.card (X 7) := by
  rw [X.card_X_eight, X.card_X_six, X.card_X_seven]

/-- GUT top-term Fibonacci alignment.
    cor:fold6-tail-offsets-gut-top-terms -/
theorem paper_gut_fibonacci_alignment :
    (24 = Nat.fib 8 + Nat.fib 4) ∧
    (45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4) ∧
    (78 = Nat.fib 10 + Nat.fib 8 + Nat.fib 3) ∧
    Nat.fib 8 = 21 ∧ Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 :=
  ⟨gut_top_fibonacci_terms.1, gut_top_fibonacci_terms.2.1, gut_top_fibonacci_terms.2.2,
   fold6_tail_offsets.1, fold6_tail_offsets.2.1, fold6_tail_offsets.2.2⟩

/-- SU(5) count closure: |X_6| + |X_2| = 24 = 4!.
    cor:su5-21-plus-3-closure -/
theorem paper_su5_count_closure :
    Fintype.card (X 6) + Fintype.card (X 2) = 24 ∧
    Nat.fib 8 = Fintype.card (X 6) ∧
    Nat.fib 4 = Fintype.card (X 2) ∧
    Nat.factorial 4 = 24 := by
  refine ⟨by rw [X.card_X_six, X.card_X_two], su5_count_closure_fib.1,
    su5_count_closure_fib.2.1, by native_decide⟩

/-- Extended Zeckendorf count certificates: |X_m| = F(m+2) for m=9..12.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_zeckendorf_count_small_extended :
    Fintype.card (X 9) = Nat.fib 11 ∧
    Fintype.card (X 10) = Nat.fib 12 ∧
    Fintype.card (X 11) = Nat.fib 13 ∧
    Fintype.card (X 12) = Nat.fib 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [X.card_X_nine]; native_decide
  · rw [X.card_X_ten]; native_decide
  · rw [X.card_X_eleven]; native_decide
  · rw [X.card_X_twelve]; native_decide

/-- The unique minimal even Zeckendorf-valid triple with boundary sum 12.
    cor:sm-minimal-triple-selection-law -/
theorem sm_minimal_triple_selection_law :
    (Nat.fib 2 + Nat.fib 4 + Nat.fib 6 = 12) ∧
    (∀ m₁ m₂ m₃ : ℕ,
      2 ≤ m₁ → Even m₁ → 2 ≤ m₂ → Even m₂ → 2 ≤ m₃ → Even m₃ →
      m₁ < m₂ → m₂ < m₃ →
      Nat.fib (m₁ - 2) + Nat.fib (m₂ - 2) + Nat.fib (m₃ - 2) = 12 →
      m₂ - m₁ ≥ 2 → m₃ - m₂ ≥ 2 →
      (m₁, m₂, m₃) = (4, 6, 8)) := by
  constructor
  · native_decide
  · intro m₁ m₂ m₃ hm₁ he₁ hm₂ he₂ hm₃ he₃ h12 h23 hsum hgap12 hgap23
    obtain ⟨k₁, rfl⟩ := he₁; obtain ⟨k₂, rfl⟩ := he₂; obtain ⟨k₃, rfl⟩ := he₃
    -- Normalize: 2*k = k+k in hsum
    have hsum' : Nat.fib (2 * k₁ - 2) + Nat.fib (2 * k₂ - 2) +
        Nat.fib (2 * k₃ - 2) = 12 := by
      simpa [two_mul] using hsum
    have hk₃_le : k₃ ≤ 4 := by
      by_contra h; push_neg at h
      have hfib_ge : Nat.fib (2 * k₃ - 2) ≥ 21 := by
        calc Nat.fib (2 * k₃ - 2) ≥ Nat.fib 8 := Nat.fib_mono (by omega)
          _ = 21 := by native_decide
      linarith [Nat.zero_le (Nat.fib (2 * k₁ - 2)),
                Nat.zero_le (Nat.fib (2 * k₂ - 2))]
    have hk₁ : k₁ = 1 ∨ k₁ = 2 := by omega
    have hk₂ : k₂ = 1 ∨ k₂ = 2 ∨ k₂ = 3 := by omega
    have hk₃ : k₃ = 1 ∨ k₃ = 2 ∨ k₃ = 3 ∨ k₃ = 4 := by omega
    rcases hk₁ with rfl | rfl <;> rcases hk₂ with rfl | rfl | rfl <;>
      rcases hk₃ with rfl | rfl | rfl | rfl <;> simp_all [Nat.fib]

end Omega.GU
