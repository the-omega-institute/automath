import Mathlib.Tactic

namespace Omega.SPG.RandomBulkBoundarySaturation

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Sample space: Boolean-valued functions on `N`.
    thm:spg-random-bulk-boundary-saturation -/
def Sample (N : Type*) : Type _ := N → Bool

instance sampleFintype : Fintype (Sample N) := by
  unfold Sample
  infer_instance

instance sampleDecEq : DecidableEq (Sample N) := by
  unfold Sample
  infer_instance

/-- Uniform expectation over Bool samples, valued in ℚ.
    thm:spg-random-bulk-boundary-saturation -/
noncomputable def expectation (X : Sample N → ℚ) : ℚ :=
  (∑ ω : Sample N, X ω) / (Fintype.card (Sample N) : ℚ)

/-- Bool indicator.
    thm:spg-random-bulk-boundary-saturation -/
def indicator (b : Bool) : ℚ := if b then 1 else 0

/-- Bit-flip equivalence at coordinate `i`.
    thm:spg-random-bulk-boundary-saturation -/
def flipAt (i : N) : Sample N ≃ Sample N where
  toFun ω := Function.update ω i (!ω i)
  invFun ω := Function.update ω i (!ω i)
  left_inv ω := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_self, Bool.not_not]
    · simp [Function.update_of_ne hj]
  right_inv ω := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_self, Bool.not_not]
    · simp [Function.update_of_ne hj]

omit [Fintype N] in
/-- Value at `i` after flipping equals `!` of the original.
    thm:spg-random-bulk-boundary-saturation -/
theorem flipAt_apply_self (i : N) (ω : Sample N) : (flipAt i ω) i = !ω i := by
  show Function.update ω i (!ω i) i = !ω i
  simp [Function.update_self]

omit [Fintype N] in
/-- Flipping at `i` leaves other coordinates fixed.
    thm:spg-random-bulk-boundary-saturation -/
theorem flipAt_apply_other (i j : N) (hij : j ≠ i) (ω : Sample N) :
    (flipAt i ω) j = ω j := by
  show Function.update ω i (!ω i) j = ω j
  exact Function.update_of_ne hij _ _

/-- Indicator at `true` plus indicator at `false` equals `1`.
    thm:spg-random-bulk-boundary-saturation -/
theorem indicator_add_not (b : Bool) : indicator b + indicator (!b) = 1 := by
  cases b <;> simp [indicator]

/-- Fintype card of `Sample N` is positive (since `Sample N = N → Bool`).
    thm:spg-random-bulk-boundary-saturation -/
theorem sample_card_pos : 0 < (Fintype.card (Sample N) : ℚ) := by
  have hne : Nonempty (Sample N) := ⟨fun _ => false⟩
  have : 0 < Fintype.card (Sample N) := Fintype.card_pos
  exact_mod_cast this

/-- Single-bit expectation: `E[1_{ω i = true}] = 1/2`.
    thm:spg-random-bulk-boundary-saturation -/
theorem expectation_single_bit (i : N) :
    expectation (fun ω : Sample N => indicator (ω i)) = 1 / 2 := by
  -- Strategy: use the flip involution to show the sum equals card/2.
  have hequiv : (∑ ω : Sample N, indicator (ω i)) =
      (∑ ω : Sample N, indicator ((flipAt i ω) i)) :=
    (Equiv.sum_comp (flipAt i) (fun ω => indicator (ω i))).symm
  have hflip : ∀ ω : Sample N,
      indicator ((flipAt i ω) i) = indicator (!ω i) := by
    intro ω
    rw [flipAt_apply_self]
  have hsum_neg :
      (∑ ω : Sample N, indicator ((flipAt i ω) i))
        = ∑ ω : Sample N, indicator (!ω i) := by
    apply Finset.sum_congr rfl
    intro ω _
    exact hflip ω
  have htotal : (∑ ω : Sample N, (indicator (ω i) + indicator (!ω i))) =
      (Fintype.card (Sample N) : ℚ) := by
    rw [show (∑ ω : Sample N, (indicator (ω i) + indicator (!ω i))) =
          ∑ _ω : Sample N, (1 : ℚ) from
        Finset.sum_congr rfl (fun ω _ => indicator_add_not (ω i))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsum : (∑ ω : Sample N, indicator (ω i))
      + (∑ ω : Sample N, indicator (!ω i)) = (Fintype.card (Sample N) : ℚ) := by
    rw [← Finset.sum_add_distrib]
    exact htotal
  have heq : (∑ ω : Sample N, indicator (ω i))
      = (∑ ω : Sample N, indicator (!ω i)) := by
    rw [hequiv, hsum_neg]
  have hdouble : 2 * (∑ ω : Sample N, indicator (ω i))
      = (Fintype.card (Sample N) : ℚ) := by
    have := hsum
    rw [heq] at this
    linarith
  unfold expectation
  have hpos := @sample_card_pos N _ _
  field_simp
  linarith [hdouble]

/-- Two-bit XOR expectation: `E[1_{ω i ⊕ ω j}] = 1/2` when `i ≠ j`.
    thm:spg-random-bulk-boundary-saturation -/
theorem expectation_xor_two (i j : N) (_hij : i ≠ j) :
    expectation (fun ω : Sample N => indicator (xor (ω i) (ω j))) = 1 / 2 := by
  -- Same flip-at-i strategy: flipping bit i flips the XOR.
  have hequiv : (∑ ω : Sample N, indicator (xor (ω i) (ω j))) =
      (∑ ω : Sample N, indicator (xor ((flipAt i ω) i) ((flipAt i ω) j))) :=
    (Equiv.sum_comp (flipAt i) (fun ω => indicator (xor (ω i) (ω j)))).symm
  have hflip : ∀ ω : Sample N,
      xor ((flipAt i ω) i) ((flipAt i ω) j) = !(xor (ω i) (ω j)) := by
    intro ω
    have h1 : (flipAt i ω) i = !ω i := flipAt_apply_self i ω
    have h2 : (flipAt i ω) j = ω j :=
      flipAt_apply_other i j (Ne.symm _hij) ω
    rw [h1, h2]
    cases ω i <;> cases ω j <;> rfl
  have hsum_neg :
      (∑ ω : Sample N, indicator (xor ((flipAt i ω) i) ((flipAt i ω) j)))
        = ∑ ω : Sample N, indicator (!(xor (ω i) (ω j))) :=
    Finset.sum_congr rfl (fun ω _ => by rw [hflip ω])
  have htotal : (∑ ω : Sample N,
      (indicator (xor (ω i) (ω j)) + indicator (!(xor (ω i) (ω j)))))
      = (Fintype.card (Sample N) : ℚ) := by
    rw [show (∑ ω : Sample N,
        (indicator (xor (ω i) (ω j)) + indicator (!(xor (ω i) (ω j))))) =
          ∑ _ω : Sample N, (1 : ℚ) from
        Finset.sum_congr rfl (fun ω _ => indicator_add_not (xor (ω i) (ω j)))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsum : (∑ ω : Sample N, indicator (xor (ω i) (ω j)))
      + (∑ ω : Sample N, indicator (!(xor (ω i) (ω j))))
      = (Fintype.card (Sample N) : ℚ) := by
    rw [← Finset.sum_add_distrib]
    exact htotal
  have heq : (∑ ω : Sample N, indicator (xor (ω i) (ω j)))
      = (∑ ω : Sample N, indicator (!(xor (ω i) (ω j)))) := by
    rw [hequiv, hsum_neg]
  have hdouble : 2 * (∑ ω : Sample N, indicator (xor (ω i) (ω j)))
      = (Fintype.card (Sample N) : ℚ) := by
    have := hsum
    rw [heq] at this
    linarith
  unfold expectation
  have hpos := @sample_card_pos N _ _
  field_simp
  linarith [hdouble]

/-- Linearity: expectation commutes with finite sums over an index set.
    thm:spg-random-bulk-boundary-saturation -/
theorem expectation_sum {β : Type*} (F : Finset β) (f : β → Sample N → ℚ) :
    expectation (fun ω => ∑ b ∈ F, f b ω) = ∑ b ∈ F, expectation (f b) := by
  unfold expectation
  rw [← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]

/-- Paper package (expectation identity, first part).
    Packaged version: the bulk-boundary expectation equals `|F|/2`
    when each boundary term is a XOR of two distinct coordinates.
    thm:spg-random-bulk-boundary-saturation -/
theorem paper_spg_random_bulk_boundary_saturation_expectation
    {β : Type*} (F : Finset β) (pair : β → N × N)
    (hpair : ∀ b ∈ F, (pair b).1 ≠ (pair b).2) :
    expectation (fun ω : Sample N =>
      ∑ b ∈ F, indicator (xor (ω (pair b).1) (ω (pair b).2))) =
      (F.card : ℚ) / 2 := by
  rw [expectation_sum]
  rw [show (∑ b ∈ F, expectation
      (fun ω => indicator (xor (ω (pair b).1) (ω (pair b).2)))) =
        ∑ _b ∈ F, ((1 : ℚ) / 2) from
      Finset.sum_congr rfl (fun b hb =>
        expectation_xor_two (pair b).1 (pair b).2 (hpair b hb))]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end Omega.SPG.RandomBulkBoundarySaturation
