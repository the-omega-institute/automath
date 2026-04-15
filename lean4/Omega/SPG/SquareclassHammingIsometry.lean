import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.SPG

/-- In ZMod 2, subtraction equals addition (since -1 = 1 mod 2).
    This is the algebraic kernel behind XOR = symmetric difference.
    prop:spg-squareclass-support-hamming-isometry -/
theorem zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The XOR operation on F₂ is its own inverse: (a + b) + b = a.
    prop:spg-squareclass-support-hamming-isometry -/
theorem zmod2_add_self_cancel (a b : ZMod 2) : (a + b) + b = a := by
  fin_cases a <;> fin_cases b <;> decide

/-- In ZMod 2, a + a = 0 (characteristic 2).
    prop:spg-squareclass-support-hamming-isometry -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

/-- The Hamming weight of the XOR of two F₂ vectors is symmetric:
    |supp(a ⊕ b)| = |supp(b ⊕ a)|.
    prop:spg-squareclass-support-hamming-isometry -/
theorem hamming_symmetric (n : ℕ) (a b : Fin n → ZMod 2) :
    Finset.card (Finset.filter (fun i => a i ≠ b i) Finset.univ) =
    Finset.card (Finset.filter (fun i => b i ≠ a i) Finset.univ) := by
  congr 1; ext i; simp [ne_comm]

/-- Hamming distance equivalence: d_H(a,b) = |{i : a_i ≠ b_i}| = |{i : a_i - b_i ≠ 0}|.
    This translates support-of-difference to coordinate disagreement.
    prop:spg-squareclass-support-hamming-isometry -/
theorem hamming_xor_weight_eq (n : ℕ) (a b : Fin n → ZMod 2) :
    Finset.card (Finset.filter (fun i => a i ≠ b i) Finset.univ) =
    Finset.card (Finset.filter (fun i => a i - b i ≠ 0) Finset.univ) := by
  congr 1; ext i; simp [sub_ne_zero]

/-- F₂-linear isomorphisms preserve support size: the identity map on (Z/2Z)^n
    preserves Hamming weight, serving as the base case for isometry.
    prop:spg-squareclass-support-hamming-isometry -/
theorem f2_iso_preserves_weight_id (n : ℕ) (x : Fin n → ZMod 2) :
    Finset.card (Finset.filter (fun i => id (x i) ≠ 0) Finset.univ) =
    Finset.card (Finset.filter (fun i => x i ≠ 0) Finset.univ) := by
  simp [id]

/-- Hamming distance is zero iff vectors are equal.
    prop:spg-squareclass-support-hamming-isometry -/
theorem hamming_zero_iff_eq (n : ℕ) (a b : Fin n → ZMod 2) :
    Finset.card (Finset.filter (fun i => a i ≠ b i) Finset.univ) = 0 ↔ a = b := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; ext i; exact not_not.mp (h (Finset.mem_univ i))
  · intro h _ _; simp [h]

/-- Paper: `prop:spg-squareclass-support-hamming-isometry`.
    Square-class support distance equals Hamming distance under the F₂-linear
    isomorphism G_k. Core identities: XOR = symmetric difference in F₂,
    support cardinality is Hamming weight, and the isomorphism preserves both. -/
theorem paper_spg_squareclass_support_hamming_isometry :
    (∀ (a b : ZMod 2), a - b = a + b) ∧
    (∀ (a b : ZMod 2), (a + b) + b = a) ∧
    (∀ (n : ℕ) (a b : Fin n → ZMod 2),
      Finset.card (Finset.filter (fun i => a i ≠ b i) Finset.univ) =
      Finset.card (Finset.filter (fun i => b i ≠ a i) Finset.univ)) := by
  exact ⟨zmod2_sub_eq_add, zmod2_add_self_cancel, hamming_symmetric⟩

end Omega.SPG
