import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The concrete affine scale used to separate the two last-bit sectors. -/
def xiZGPrimorialBase (B : ℕ) : ℕ :=
  B + 2

/-- The address offset attached to length `n`. -/
def xiZGPrimorialShift (B n : ℕ) : ℕ :=
  xiZGPrimorialBase B ^ n

/-- The affine embedding that shifts a lower-level address block into the last-bit-`1` sector. -/
def xiZGPrimorialShiftEmbedding (B n : ℕ) : ℕ ↪ ℕ where
  toFun x := xiZGPrimorialShift B n + x
  inj' _ _ h := Nat.add_left_cancel h

/-- Recursive address family for admissible binary prefixes: either append a last bit `0`, or
append a last bit `1` after forcing the previous bit to be `0`, represented by the affine shift.
-/
def xiZGPrimorialAddressFamily (B : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | 1 => {0, 1}
  | n + 2 =>
      xiZGPrimorialAddressFamily B (n + 1) ∪
        (xiZGPrimorialAddressFamily B n).map (xiZGPrimorialShiftEmbedding B (n + 1))

lemma xiZGPrimorialShift_step_le (B n : ℕ) :
    xiZGPrimorialShift B n ≤ xiZGPrimorialShift B (n + 1) := by
  calc
    xiZGPrimorialShift B n = xiZGPrimorialShift B n * 1 := by simp
    _ ≤ xiZGPrimorialShift B n * xiZGPrimorialBase B := by
      exact Nat.mul_le_mul_left _ (by simp [xiZGPrimorialBase])
    _ = xiZGPrimorialShift B (n + 1) := by
      simp [xiZGPrimorialShift, pow_succ, Nat.mul_comm]

lemma xiZGPrimorialShift_double_step_le (B n : ℕ) :
    2 * xiZGPrimorialShift B (n + 1) ≤ xiZGPrimorialShift B (n + 2) := by
  calc
    2 * xiZGPrimorialShift B (n + 1) ≤
        xiZGPrimorialBase B * xiZGPrimorialShift B (n + 1) := by
      exact Nat.mul_le_mul_right _ (by simp [xiZGPrimorialBase])
    _ = xiZGPrimorialShift B (n + 2) := by
      simp [xiZGPrimorialShift, pow_succ, Nat.mul_comm]

lemma xiZGPrimorialAddress_lt_shift (B : ℕ) : ∀ n {x : ℕ},
    x ∈ xiZGPrimorialAddressFamily B n → x < xiZGPrimorialShift B n
  | 0, x, hx => by
      simp [xiZGPrimorialAddressFamily, xiZGPrimorialShift] at hx ⊢
      omega
  | 1, x, hx => by
      simp [xiZGPrimorialAddressFamily, xiZGPrimorialShift, xiZGPrimorialBase] at hx ⊢
      omega
  | n + 2, x, hx => by
      simp only [xiZGPrimorialAddressFamily, Finset.mem_union, Finset.mem_map] at hx
      rcases hx with hx | hx
      · have hx' : x < xiZGPrimorialShift B (n + 1) :=
          xiZGPrimorialAddress_lt_shift B (n + 1) hx
        exact lt_of_lt_of_le hx' (xiZGPrimorialShift_step_le B (n + 1))
      · rcases hx with ⟨y, hy, rfl⟩
        have hy' : y < xiZGPrimorialShift B n := xiZGPrimorialAddress_lt_shift B n hy
        have hmono : xiZGPrimorialShift B n ≤ xiZGPrimorialShift B (n + 1) :=
          xiZGPrimorialShift_step_le B n
        have hdouble : 2 * xiZGPrimorialShift B (n + 1) ≤ xiZGPrimorialShift B (n + 2) :=
          xiZGPrimorialShift_double_step_le B n
        have hsum :
            xiZGPrimorialShift B (n + 1) + y <
              xiZGPrimorialShift B (n + 1) + xiZGPrimorialShift B n :=
          Nat.add_lt_add_left hy' _
        have hle :
            xiZGPrimorialShift B (n + 1) + xiZGPrimorialShift B n ≤
              xiZGPrimorialShift B (n + 1) + xiZGPrimorialShift B (n + 1) :=
          Nat.add_le_add_left hmono _
        have hlt :
            xiZGPrimorialShift B (n + 1) + y < 2 * xiZGPrimorialShift B (n + 1) := by
          exact lt_of_lt_of_le hsum (by simpa [two_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hle)
        exact lt_of_lt_of_le hlt hdouble

lemma xiZGPrimorialAddress_disjoint (B n : ℕ) :
    Disjoint (xiZGPrimorialAddressFamily B (n + 1))
      ((xiZGPrimorialAddressFamily B n).map (xiZGPrimorialShiftEmbedding B (n + 1))) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx1 hx2
  simp only [Finset.mem_map] at hx2
  rcases hx2 with ⟨y, hy, rfl⟩
  have hupper : xiZGPrimorialShift B (n + 1) + y < xiZGPrimorialShift B (n + 1) :=
    xiZGPrimorialAddress_lt_shift B (n + 1) hx1
  exact (Nat.not_lt_of_ge (Nat.le_add_right _ _)) hupper

lemma xiZGPrimorialAddress_card_rec (B n : ℕ) :
    (xiZGPrimorialAddressFamily B (n + 2)).card =
      (xiZGPrimorialAddressFamily B (n + 1)).card + (xiZGPrimorialAddressFamily B n).card := by
  rw [xiZGPrimorialAddressFamily, Finset.card_union_of_disjoint (xiZGPrimorialAddress_disjoint B n),
    Finset.card_map]

lemma xiZGPrimorialAddress_card_eq_fib (B : ℕ) : ∀ n,
    (xiZGPrimorialAddressFamily B n).card = Nat.fib (n + 2)
  | 0 => by
      simp [xiZGPrimorialAddressFamily]
  | 1 => by
      norm_num [xiZGPrimorialAddressFamily, Nat.fib]
  | n + 2 => by
      rw [xiZGPrimorialAddress_card_rec, xiZGPrimorialAddress_card_eq_fib B (n + 1),
        xiZGPrimorialAddress_card_eq_fib B n]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.fib_add_two (n := n + 2)).symm

/-- Concrete statement for the primorial/Fibonacci affine recursion: the shift map is injective,
the two last-bit sectors are disjoint, the address family splits as their union, and the
cardinality therefore follows the Fibonacci recurrence.
    thm:xi-time-part9g-zg-primorial-fibonacci-affine-recursion -/
def XiTimePart9gZGPrimorialFibonacciAffineRecursionStatement (B n : ℕ) : Prop :=
  Function.Injective (xiZGPrimorialShiftEmbedding B (n + 1)) ∧
    Disjoint (xiZGPrimorialAddressFamily B (n + 1))
      ((xiZGPrimorialAddressFamily B n).map (xiZGPrimorialShiftEmbedding B (n + 1))) ∧
    xiZGPrimorialAddressFamily B (n + 2) =
      xiZGPrimorialAddressFamily B (n + 1) ∪
        (xiZGPrimorialAddressFamily B n).map (xiZGPrimorialShiftEmbedding B (n + 1)) ∧
    (xiZGPrimorialAddressFamily B (n + 2)).card =
      (xiZGPrimorialAddressFamily B (n + 1)).card + (xiZGPrimorialAddressFamily B n).card ∧
    (xiZGPrimorialAddressFamily B n).card = Nat.fib (n + 2)

theorem paper_xi_time_part9g_zg_primorial_fibonacci_affine_recursion (B n : ℕ) :
    XiTimePart9gZGPrimorialFibonacciAffineRecursionStatement B n := by
  refine ⟨(xiZGPrimorialShiftEmbedding B (n + 1)).injective, xiZGPrimorialAddress_disjoint B n,
    rfl, xiZGPrimorialAddress_card_rec B n, xiZGPrimorialAddress_card_eq_fib B n⟩

end Omega.Zeta
