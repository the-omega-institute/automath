import Omega.Folding.StableSyntax
import Mathlib.Algebra.BigOperators.Fin

namespace Omega

/-- The Fibonacci-weighted value used by the paper's folding map. -/
def weight : {m : Nat} → Word m → Nat
  | 0, _ => 0
  | m + 1, w =>
      weight (truncate w) + if w ⟨m, Nat.lt_succ_self m⟩ then Nat.fib (m + 2) else 0

@[simp] theorem weight_empty : weight (m := 0) (fun i => False.elim (Nat.not_lt_zero _ i.isLt)) = 0 :=
  rfl

@[simp] theorem weight_snoc (w : Word m) (b : Bool) :
    weight (snoc w b) = weight w + if b then Nat.fib (m + 2) else 0 := by
  simp [weight, truncate_snoc, snoc_last]

@[simp] theorem weight_appendFalse (x : X m) :
    weight (X.appendFalse x).1 = weight x.1 := by
  simp [X.appendFalse, weight_snoc]

@[simp] theorem weight_appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) :
    weight (X.appendTrue x hLast).1 = weight x.1 + Nat.fib (m + 2) := by
  simp [X.appendTrue, weight_snoc]


/-- Weight of a stable word ending in false equals weight of its restriction. -/
theorem weight_of_lastFalse {w : Word (m + 1)} (h : w ⟨m, Nat.lt_succ_self m⟩ = false) :
    weight w = weight (truncate w) := by
  simp [weight, h]

/-- Weight of a stable word ending in true equals weight of restriction + F(m+2). -/
theorem weight_of_lastTrue {w : Word (m + 1)} (h : w ⟨m, Nat.lt_succ_self m⟩ = true) :
    weight w = weight (truncate w) + Nat.fib (m + 2) := by
  simp [weight, h]

/-- Weight is monotone: adding a true bit increases weight. -/
theorem weight_pos_of_bit_true {w : Word (m + 1)} (h : w ⟨m, Nat.lt_succ_self m⟩ = true) :
    0 < weight w := by
  rw [weight_of_lastTrue h]
  exact Nat.lt_of_lt_of_le (fib_succ_pos (m + 1)) (Nat.le_add_left _ _)

/-- Weight of a length-1 word is 0 or F(2) = 1. -/
theorem weight_word_one (w : Word 1) :
    weight w = if w ⟨0, Nat.zero_lt_one⟩ then 1 else 0 := by
  simp [weight]


/-- Weight of the all-false word is 0.
    lem:weight-allFalse -/
@[simp] theorem weight_allFalse : weight (fun _ : Fin m => false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [weight, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    convert ih using 2

/-- weight(w) = Σ_{i : Fin m} (if w i then Nat.fib (i+2) else 0).
    def:pom-fiber-adm-path -/
theorem weight_eq_fib_ite_sum {m : Nat} (w : Word m) :
    weight w = ∑ i : Fin m, if w i then Nat.fib (i.val + 2) else 0 := by
  induction m with
  | zero => simp [weight]
  | succ m ih =>
    rw [weight, ih (truncate w), Fin.sum_univ_castSucc (n := m)]
    congr 1

-- ══════════════════════════════════════════════════════════════
-- Phase 180
-- ══════════════════════════════════════════════════════════════

/-- Weight is positive iff the word has at least one true bit. -/
theorem weight_pos_iff_exists_true (w : Word m) :
    0 < weight w ↔ ∃ i : Fin m, w i = true := by
  constructor
  · -- (→) weight > 0 → ∃ true bit. Contrapositive: all false → weight = 0.
    intro hw
    by_contra h; push_neg at h
    have : w = fun _ => false := funext fun i => by
      cases hi : w i
      · rfl
      · exact absurd hi (by simp [h i])
    rw [this, weight_allFalse] at hw; omega
  · -- (←) ∃ true bit → weight > 0.
    rintro ⟨i, hi⟩
    rw [weight_eq_fib_ite_sum]
    -- Split sum at i: fib(i+2) + rest ≥ fib(i+2) > 0
    calc 0 < Nat.fib (i.val + 2) := fib_succ_pos (i.val + 1)
      _ ≤ ∑ j : Fin m, if w j then Nat.fib (j.val + 2) else 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          simp [hi]

/-- The all-false word is the unique word of weight zero. -/
theorem weight_zero_iff_allFalse (w : Word m) :
    weight w = 0 ↔ w = fun _ => false := by
  constructor
  · intro hw
    have hno := mt (weight_pos_iff_exists_true w).mpr (by omega)
    push_neg at hno
    funext i; exact Bool.eq_false_iff.mpr (hno i)
  · intro h; rw [h, weight_allFalse]

/-- Flipping a single bit from false to true increases weight by F_{i+2}. -/
theorem weight_update_true_add (w : Word m) (i : Fin m) (hi : w i = false) :
    weight (Function.update w i true) = weight w + Nat.fib (i.val + 2) := by
  simp only [weight_eq_fib_ite_sum]
  rw [show ∑ j : Fin m, (if Function.update w i true j then Nat.fib (j.val + 2) else 0) =
      ∑ j : Fin m, (if w j then Nat.fib (j.val + 2) else 0) +
      Nat.fib (i.val + 2) - 0 from by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    have hrest : ∀ j ∈ Finset.univ.erase i,
        (if Function.update w i true j then Nat.fib (j.val + 2) else 0) =
        (if w j then Nat.fib (j.val + 2) else 0) := by
      intro j hj
      rw [Finset.mem_erase] at hj
      rw [Function.update_of_ne hj.1]
    rw [Finset.sum_congr rfl hrest, hi]; simp; omega]
  omega

end Omega
