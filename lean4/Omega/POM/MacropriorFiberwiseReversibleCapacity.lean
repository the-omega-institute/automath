import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin

namespace Omega.POM

universe u

section

variable {X : Type u} [Fintype X]

/-- The microstate space with fiber sizes `d x`. -/
abbrev FiberState (d : X → ℕ) := Σ x : X, Fin (d x)

/-- The states in the fiber over `x` that are recovered exactly by the given encoder/decoder. -/
abbrev RecoverableStates (d : X → ℕ) (L : ℕ)
    (enc : FiberState d → Fin L) (dec : (x : X) → Fin L → Fin (d x)) (x : X) :=
  {i : Fin (d x) // dec x (enc ⟨x, i⟩) = i}

/-- The number of exactly recoverable states in the fiber over `x`. -/
abbrev recoverableCount (d : X → ℕ) (L : ℕ)
    (enc : FiberState d → Fin L) (dec : (x : X) → Fin L → Fin (d x)) (x : X) : ℕ :=
  Fintype.card (RecoverableStates d L enc dec x)

lemma recoverableCount_le_fiber (d : X → ℕ) (L : ℕ)
    (enc : FiberState d → Fin L) (dec : (x : X) → Fin L → Fin (d x)) (x : X) :
    recoverableCount d L enc dec x ≤ d x := by
  simpa [recoverableCount, RecoverableStates] using
    (Fintype.card_le_of_injective (fun i : RecoverableStates d L enc dec x => i.1)
      (fun _ _ h => Subtype.ext h))

lemma recoverableCount_le_codes (d : X → ℕ) (L : ℕ)
    (enc : FiberState d → Fin L) (dec : (x : X) → Fin L → Fin (d x)) (x : X) :
    recoverableCount d L enc dec x ≤ L := by
  let code : RecoverableStates d L enc dec x → Fin L := fun i => enc ⟨x, i.1⟩
  have hcode : Function.Injective code := by
    intro i j hij
    apply Subtype.ext
    calc
      i.1 = dec x (enc ⟨x, i.1⟩) := by simpa using i.2.symm
      _ = dec x (enc ⟨x, j.1⟩) := by simpa [code] using congrArg (fun b => dec x b) hij
      _ = j.1 := by simpa using j.2
  simpa [recoverableCount, code] using Fintype.card_le_of_injective code hcode

/-- The canonical optimal encoder: keep the index when it fits into `Fin L`, otherwise collapse
to the default code `0`. -/
def optimalEnc (d : X → ℕ) (L : ℕ) (hL : 0 < L) : FiberState d → Fin L
  | ⟨_, i⟩ =>
      if hi : (i : ℕ) < L then ⟨i, hi⟩ else ⟨0, hL⟩

/-- The canonical optimal decoder: read the code back as an index whenever that index lies in the
fiber, otherwise return the default state `0` in the fiber. -/
def optimalDec (d : X → ℕ) (L : ℕ) (hd : ∀ x, 0 < d x) : (x : X) → Fin L → Fin (d x)
  | x, b =>
      if hb : (b : ℕ) < d x then ⟨b, hb⟩ else ⟨0, hd x⟩

lemma optimalDec_optimalEnc_eq_iff_lt (d : X → ℕ) (hd : ∀ x, 0 < d x) (L : ℕ) (hL : 0 < L)
    (x : X) (i : Fin (d x)) :
    optimalDec d L hd x (optimalEnc d L hL ⟨x, i⟩) = i ↔ (i : ℕ) < L := by
  by_cases hi : (i : ℕ) < L
  · simp [optimalEnc, optimalDec, hi, i.isLt]
  · have hLi : L ≤ (i : ℕ) := Nat.le_of_not_gt hi
    have hiPos : 0 < (i : ℕ) := lt_of_lt_of_le hL hLi
    have hne : (i : ℕ) ≠ 0 := Nat.ne_of_gt hiPos
    have hneFin : (⟨0, hd x⟩ : Fin (d x)) ≠ i := by
      intro hEq
      exact hne (congrArg Fin.val hEq).symm
    simp [optimalEnc, optimalDec, hi, hd x, hneFin]

def optimalRecoverableStatesEquiv (d : X → ℕ) (hd : ∀ x, 0 < d x) (L : ℕ) (hL : 0 < L)
    (x : X) :
    RecoverableStates d L (optimalEnc d L hL) (optimalDec d L hd) x ≃
      {i : Fin (d x) // (i : ℕ) < L} where
  toFun i := ⟨i.1, (optimalDec_optimalEnc_eq_iff_lt d hd L hL x i.1).1 i.2⟩
  invFun i := ⟨i.1, (optimalDec_optimalEnc_eq_iff_lt d hd L hL x i.1).2 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma optimal_recoverableCount (d : X → ℕ) (hd : ∀ x, 0 < d x) (L : ℕ) (hL : 0 < L) (x : X) :
    recoverableCount d L (optimalEnc d L hL) (optimalDec d L hd) x = Nat.min (d x) L := by
  calc
    recoverableCount d L (optimalEnc d L hL) (optimalDec d L hd) x
        = Fintype.card {i : Fin (d x) // (i : ℕ) < L} := by
            exact Fintype.card_congr (optimalRecoverableStatesEquiv d hd L hL x)
    _ = Nat.min (d x) L := by
      calc
        Fintype.card {i : Fin (d x) // (i : ℕ) < L}
            = (Finset.univ.filter fun i : Fin (d x) => (i : ℕ) < L).card := by
                apply Fintype.card_of_subtype
                intro i
                simp
        _ = Nat.min (d x) L := by
          simpa using (Fin.card_filter_val_lt (n := d x) (m := L))

/-- Paper-facing combinatorial package for fiberwise reversible capacity under an arbitrary
nonnegative macroprior. The theorem records the pointwise cardinality bound, its weighted
macroprior sum, and an explicit encoder/decoder attaining equality fiberwise.
    thm:pom-macroprior-fiberwise-reversible-capacity -/
theorem paper_pom_macroprior_fiberwise_reversible_capacity
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (L : ℕ) (hL : 0 < L) :
    (∀ enc dec x, recoverableCount d L enc dec x ≤ Nat.min (d x) L) ∧
    (∀ w : X → ℕ, ∀ enc dec,
      (∑ x, w x * recoverableCount d L enc dec x) ≤ ∑ x, w x * Nat.min (d x) L) ∧
    ∃ enc dec,
      (∀ x, recoverableCount d L enc dec x = Nat.min (d x) L) ∧
      ∀ w : X → ℕ, (∑ x, w x * recoverableCount d L enc dec x) = ∑ x, w x * Nat.min (d x) L := by
  refine ⟨?_, ?_, ?_⟩
  · intro enc dec x
    by_cases hdx : d x ≤ L
    · simpa [Nat.min_eq_left hdx] using recoverableCount_le_fiber d L enc dec x
    · have hLx : L ≤ d x := Nat.le_of_lt (lt_of_not_ge hdx)
      simpa [Nat.min_eq_right hLx] using recoverableCount_le_codes d L enc dec x
  · intro w enc dec
    refine Finset.sum_le_sum ?_
    intro x hx
    have hbound : recoverableCount d L enc dec x ≤ Nat.min (d x) L := by
      by_cases hdx : d x ≤ L
      · simpa [Nat.min_eq_left hdx] using recoverableCount_le_fiber d L enc dec x
      · have hLx : L ≤ d x := Nat.le_of_lt (lt_of_not_ge hdx)
        simpa [Nat.min_eq_right hLx] using recoverableCount_le_codes d L enc dec x
    exact Nat.mul_le_mul_left (w x) hbound
  · refine ⟨optimalEnc d L hL, optimalDec d L hd, ?_, ?_⟩
    · intro x
      exact optimal_recoverableCount d hd L hL x
    · intro w
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [optimal_recoverableCount d hd L hL x]

end

end Omega.POM
