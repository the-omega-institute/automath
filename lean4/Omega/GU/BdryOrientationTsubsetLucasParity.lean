import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Boundary orientation `t`-subset Lucas parity

This file formalizes the mod-2 Lucas criterion for binomial coefficients in a binary test-bit form.
-/

namespace Omega.GU.BdryOrientationTsubsetLucasParity

open Nat

/-- One binary Lucas step: the parity of a binomial coefficient factors into the low-bit comparison
and the parity of the quotient-level binomial coefficient.
    cor:bdry-orientation-tsubset-lucas-parity -/
lemma odd_choose_bit_bit_iff (a0 b0 : Bool) (a b : ℕ) :
    Odd (Nat.choose (Nat.bit a0 a) (Nat.bit b0 b)) ↔ (b0 → a0) ∧ Odd (Nat.choose a b) := by
  have hmod : Nat.choose (Nat.bit a0 a) (Nat.bit b0 b) % 2 =
      (Nat.choose ((Nat.bit a0 a) % 2) ((Nat.bit b0 b) % 2) *
        Nat.choose ((Nat.bit a0 a) / 2) ((Nat.bit b0 b) / 2)) % 2 := by
    simpa using
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := Nat.bit a0 a) (k := Nat.bit b0 b) (p := 2))
  rw [Nat.odd_iff, hmod, ← Nat.odd_iff, Nat.odd_mul]
  cases a0 <;> cases b0
  · simp
  · simp
  · have h : (((2 * a + 1) / 2).choose b) = a.choose b := by
      rw [show (2 * a + 1) / 2 = a by omega]
    simp [h]
  · have h : (((2 * a + 1) / 2).choose ((2 * b + 1) / 2)) = a.choose b := by
      rw [show (2 * a + 1) / 2 = a by omega, show (2 * b + 1) / 2 = b by omega]
    simp [h]

/-- Bitwise subset relation for binary constructors.
    cor:bdry-orientation-tsubset-lucas-parity -/
lemma bit_subset_iff (a0 b0 : Bool) (a b : ℕ) :
    (∀ i, (Nat.bit b0 b).testBit i → (Nat.bit a0 a).testBit i) ↔
      (b0 → a0) ∧ ∀ i, b.testBit i → a.testBit i := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h 0
    · intro i
      simpa [Nat.testBit_bit_succ] using h (i + 1)
  · rintro ⟨h0, htail⟩ i
    cases i with
    | zero => simpa using h0
    | succ i => simpa [Nat.testBit_bit_succ] using htail i

/-- Global binary Lucas criterion: a binomial coefficient is odd exactly when every active bit of
the lower index is also active in the upper index.
    cor:bdry-orientation-tsubset-lucas-parity -/
theorem odd_choose_iff_testBit_subset (a : ℕ) :
    ∀ b, Odd (Nat.choose a b) ↔ ∀ i, b.testBit i → a.testBit i := by
  induction a using Nat.binaryRec with
  | zero =>
      intro b
      constructor
      · intro h i hbi
        have hb0 : b = 0 := by
          by_contra hb0
          have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
          have hchoose : Nat.choose 0 b = 0 := Nat.choose_eq_zero_of_lt hbpos
          rw [hchoose] at h
          simp at h
        subst hb0
        simp at hbi
      · intro h
        have hb0 : b = 0 := Nat.zero_of_testBit_eq_false fun i => by
          by_cases hbi : b.testBit i = true
          · exact False.elim (by simpa using h i hbi)
          · simpa using hbi
        subst hb0
        simp
  | bit a0 a ih =>
      intro b
      refine Nat.bitCasesOn
        (motive := fun b => Odd (Nat.choose (Nat.bit a0 a) b) ↔
          ∀ i, b.testBit i → (Nat.bit a0 a).testBit i) b ?_
      intro b0 n
      rw [odd_choose_bit_bit_iff, bit_subset_iff, ih n]

set_option maxHeartbeats 400000 in
/-- Paper seed: Lucas parity criterion in pure test-bit form.
    cor:bdry-orientation-tsubset-lucas-parity -/
theorem paper_bdry_orientation_tsubset_lucas_parity_seeds (a b : ℕ) :
    Odd (Nat.choose a b) ↔ ∀ i, b.testBit i → a.testBit i := by
  simpa using odd_choose_iff_testBit_subset a b

/-- Paper-facing package clone for the Lucas parity criterion.
    cor:bdry-orientation-tsubset-lucas-parity -/
theorem paper_bdry_orientation_tsubset_lucas_parity_package (a b : ℕ) :
    Odd (Nat.choose a b) ↔ ∀ i, b.testBit i → a.testBit i :=
  paper_bdry_orientation_tsubset_lucas_parity_seeds a b

/-- Paper-facing corollary: Lucas parity in test-bit subset form.
    cor:bdry-orientation-tsubset-lucas-parity -/
theorem paper_bdry_orientation_tsubset_lucas_parity (a b : ℕ) :
    Odd (Nat.choose a b) ↔ ∀ i, b.testBit i → a.testBit i := by
  simpa using odd_choose_iff_testBit_subset a b

end Omega.GU.BdryOrientationTsubsetLucasParity
