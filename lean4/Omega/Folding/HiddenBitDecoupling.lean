import Omega.Folding.MaxFiberTwoStep
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega

/-- The unique empty word. -/
def emptyWord : Word 0 := fun i => False.elim (Nat.not_lt_zero _ i.isLt)

/-- Attach `k` copies of the bad top pair `(1,0)` above a low-order word. -/
def badTopIter : (k : Nat) → Word n → Word (n + 2 * k)
  | 0, w => by
      simpa using w
  | k + 1, w => by
      have h : Word (n + (2 * k + 2)) := by
        simpa [Nat.add_assoc] using (snoc (snoc (badTopIter k w) false) true)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The exceptional top prefix made entirely of bad pairs `(1,0)`. -/
def badTopWord (k : Nat) : Word (2 * k) := by
  simpa [Nat.zero_add] using (badTopIter k emptyWord)

theorem hiddenBit_snoc_false_true {m : Nat} (w : Word m) :
    hiddenBit (snoc (snoc w false) true) = hiddenBit w := by
  revert w
  induction m with
  | zero =>
      intro w
      have hw : w = emptyWord := by
        funext i
        exact Fin.elim0 i
      rw [hw]
      decide
  | succ m =>
      intro w
      have hLast : snoc (snoc w false) true ⟨m + 2, by omega⟩ = true := by
        simp [snoc]
      have hPenult : snoc (snoc w false) true ⟨m + 1, by omega⟩ = false := by
        simp [snoc]
      rw [hiddenBit_unified_recurrence (m := m) (w := snoc (snoc w false) true) hLast, hPenult]
      simp

theorem hiddenBit_badTopIter (k : Nat) (w : Word n) :
    hiddenBit (badTopIter k w) = hiddenBit w := by
  induction k with
  | zero =>
      simp [badTopIter]
  | succ k ih =>
      have hstep :
          hiddenBit (snoc (snoc (badTopIter k w) false) true) = hiddenBit (badTopIter k w) :=
        hiddenBit_snoc_false_true (w := badTopIter k w)
      simpa [badTopIter] using hstep.trans ih

private theorem two_pow_double (k : Nat) : 2 ^ (2 * k) = 4 ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        2 ^ (2 * (k + 1)) = 2 ^ (2 * k) * 4 := by
          rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
          norm_num
        _ = 4 ^ k * 4 := by rw [ih]
        _ = 4 ^ (k + 1) := by simp [pow_succ, mul_comm]

/-- The only way low bits can influence the hidden bit after looking at the top `2k` bits is to
see the unique bad prefix with all top pairs equal to `(1,0)`; that exceptional prefix has
uniform probability `4^{-k}`.
    thm:pom-hidden-bit-exponential-decoupling-low-bits -/
theorem paper_pom_hidden_bit_exponential_decoupling_low_bits (k n : Nat) :
    (∀ w : Word n, hiddenBit (badTopIter k w) = hiddenBit w) ∧
      (((Finset.univ.filter fun p : Word (2 * k) => p = badTopWord k).card : ℚ) /
        Fintype.card (Word (2 * k)) = (1 : ℚ) / 4 ^ k) := by
  constructor
  · intro w
    exact hiddenBit_badTopIter k w
  · have hbad : (Finset.univ.filter fun p : Word (2 * k) => p = badTopWord k).card = 1 := by
      classical
      have hsingle :
          Finset.univ.filter (fun p : Word (2 * k) => p = badTopWord k) = {badTopWord k} := by
        ext p
        simp
      rw [hsingle]
      simp
    have hcard : Fintype.card (Word (2 * k)) = 4 ^ k := by
      calc
        Fintype.card (Word (2 * k)) = 2 ^ (2 * k) := by
          simp [Word]
        _ = 4 ^ k := two_pow_double k
    rw [hbad, hcard]
    norm_num

end Omega
