import Mathlib.Tactic
import Omega.Folding.Zeckendorf

namespace Omega

namespace X

local instance : IsTrans Nat (fun a b ↦ b + 2 ≤ a) where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

/-- The raw length-`m` word cut out by a Zeckendorf index list. -/
def wordOfIndices (m : Nat) (l : List Nat) : Word m :=
  fun i => decide (i.1 + 2 ∈ l)

@[simp] theorem get_wordOfIndices_lt (l : List Nat) {i : Nat} (h : i < m) :
    get (wordOfIndices m l) i = decide (i + 2 ∈ l) := by
  simp [wordOfIndices, get, h]

@[simp] theorem get_wordOfIndices_eq_true_iff (l : List Nat) {i : Nat} (h : i < m) :
    get (wordOfIndices m l) i = true ↔ i + 2 ∈ l := by
  rw [get_wordOfIndices_lt (m := m) l h]
  simp

theorem isZeckendorfRep_tail : ∀ {a : Nat} {l : List Nat}, (a :: l).IsZeckendorfRep → l.IsZeckendorfRep
  | a, l, h => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (a :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using h
      simpa [List.IsZeckendorfRep] using hChain.tail

theorem two_le_of_mem_isZeckendorfRep :
    ∀ {l : List Nat} {a : Nat}, l.IsZeckendorfRep → a ∈ l → 2 ≤ a
  | [], _a, _hRep, hMem => by
      cases hMem
  | b :: l, a, hRep, hMem => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (b :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using hRep
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · have hRel : 0 + 2 ≤ a := hChain.rel_cons (List.mem_append_right l (by simp))
        simpa using hRel
      · exact two_le_of_mem_isZeckendorfRep (isZeckendorfRep_tail hRep) hMem

theorem not_mem_succ_of_mem_isZeckendorfRep :
    ∀ {l : List Nat} {a : Nat}, l.IsZeckendorfRep → a ∈ l → a + 1 ∉ l
  | [], _a, _hRep, hMem => by
      cases hMem
  | b :: l, a, hRep, hMem => by
      have hChain : List.IsChain (fun a b : Nat ↦ b + 2 ≤ a) (b :: (l ++ [0])) := by
        simpa [List.IsZeckendorfRep, List.cons_append] using hRep
      have hTail : l.IsZeckendorfRep := isZeckendorfRep_tail hRep
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · intro hSucc
        have hRel : (a + 1) + 2 ≤ a := hChain.rel_cons (by simpa using List.mem_append_left [0] hSucc)
        omega
      · intro hSucc
        simp only [List.mem_cons] at hSucc
        rcases hSucc with rfl | hSucc
        · have hRel : a + 2 ≤ a + 1 := by
            have hMem' : a ∈ l ++ [0] := List.mem_append_left [0] hMem
            simpa using (hChain.rel_cons hMem')
          omega
        · exact not_mem_succ_of_mem_isZeckendorfRep hTail hMem hSucc

theorem no11_wordOfIndices (m : Nat) (l : List Nat) (hRep : l.IsZeckendorfRep) :
    No11 (wordOfIndices m l) := by
  intro i hi hi1
  have hiLt : i < m := lt_of_get_eq_true hi
  have hi1Lt : i + 1 < m := lt_of_get_eq_true_succ hi1
  have hMem : i + 2 ∈ l := (get_wordOfIndices_eq_true_iff (m := m) l hiLt).1 hi
  have hMemSucc : i + 3 ∈ l := by
    simpa [Nat.add_assoc] using
      (get_wordOfIndices_eq_true_iff (m := m) l hi1Lt).1 hi1
  exact not_mem_succ_of_mem_isZeckendorfRep hRep hMem hMemSucc

/-- Truncate a Zeckendorf representation to a stable length-`m` word. -/
def ofIndices (m : Nat) (l : List Nat) (hRep : l.IsZeckendorfRep) : X m :=
  ⟨wordOfIndices m l, no11_wordOfIndices m l hRep⟩

@[simp] theorem get_ofIndices_eq_true_iff (l : List Nat) (hRep : l.IsZeckendorfRep)
    {i : Nat} (h : i < m) :
    get (ofIndices m l hRep).1 i = true ↔ i + 2 ∈ l :=
  get_wordOfIndices_eq_true_iff (m := m) l h

theorem mem_zeckIndices_iff_get_true {m : Nat} (x : X m) (i : Nat) (hi : i < m) :
    i + 2 ∈ zeckIndices x ↔ get x.1 i = true := by
  induction m generalizing i with
  | zero =>
      cases Nat.not_lt_zero _ hi
  | succ m ih =>
      by_cases hLast : Omega.last x.1 = true
      · by_cases hEq : i = m
        · subst hEq
          constructor
          · intro _hMem
            simpa [Omega.last, Omega.get] using hLast
          · intro _hBit
            simp [zeckIndices, hLast]
        · have hiLt : i < m := lt_of_le_of_ne (Nat.le_of_lt_succ hi) hEq
          constructor
          · intro hMem
            have hTailMem : i + 2 ∈ zeckIndices (restrict x) := by
              simp [zeckIndices, hLast] at hMem
              rcases hMem with hHead | hTailMem
              · omega
              · exact hTailMem
            have hRestrict : get (restrict x).1 i = true :=
              (ih (restrict x) i hiLt).1 hTailMem
            rw [restrict, truncate_get_eq (w := x.1) (i := i) hiLt] at hRestrict
            exact hRestrict
          · intro hBit
            have hRestrict : get (restrict x).1 i = true := by
              rw [restrict, truncate_get_eq (w := x.1) (i := i) hiLt]
              exact hBit
            have hTailMem : i + 2 ∈ zeckIndices (restrict x) :=
              (ih (restrict x) i hiLt).2 hRestrict
            simp [zeckIndices, hLast, hTailMem]
      · have hLastFalse : Omega.last x.1 = false := by
          cases hBit : Omega.last x.1 <;> simp [hBit] at hLast ⊢
        by_cases hEq : i = m
        · constructor
          · intro hMem
            have hTailMem : m + 2 ∈ zeckIndices (restrict x) := by
              simpa [hEq, zeckIndices, hLastFalse] using hMem
            have hLt : m + 2 < m + 2 := mem_zeckIndices_lt (restrict x) hTailMem
            omega
          · intro hBit
            have hBit' : get x.1 m = true := by
              simpa [hEq] using hBit
            have hFalse : get x.1 m = false := by
              simpa [Omega.last, Omega.get] using hLastFalse
            rw [hFalse] at hBit'
            cases hBit'
        · have hiLt : i < m := lt_of_le_of_ne (Nat.le_of_lt_succ hi) hEq
          constructor
          · intro hMem
            have hTailMem : i + 2 ∈ zeckIndices (restrict x) := by
              simpa [zeckIndices, hLastFalse] using hMem
            have hRestrict : get (restrict x).1 i = true :=
              (ih (restrict x) i hiLt).1 hTailMem
            rw [restrict, truncate_get_eq (w := x.1) (i := i) hiLt] at hRestrict
            exact hRestrict
          · intro hBit
            have hRestrict : get (restrict x).1 i = true := by
              rw [restrict, truncate_get_eq (w := x.1) (i := i) hiLt]
              exact hBit
            have hTailMem : i + 2 ∈ zeckIndices (restrict x) :=
              (ih (restrict x) i hiLt).2 hRestrict
            simpa [zeckIndices, hLastFalse] using hTailMem

theorem ofIndices_zeckIndices (x : X m) :
    ofIndices m (zeckIndices x) (zeckIndices_isZeckendorfRep x) = x := by
  apply Subtype.ext
  funext j
  have hiff :
      (ofIndices m (zeckIndices x) (zeckIndices_isZeckendorfRep x)).1 j = true ↔ x.1 j = true := by
    calc
      (ofIndices m (zeckIndices x) (zeckIndices_isZeckendorfRep x)).1 j = true
          ↔ get (ofIndices m (zeckIndices x) (zeckIndices_isZeckendorfRep x)).1 j.1 = true := by
              simp [Omega.get, j.isLt]
      _ ↔ j.1 + 2 ∈ zeckIndices x := by
            exact get_ofIndices_eq_true_iff (m := m) (l := zeckIndices x) _ j.isLt
      _ ↔ get x.1 j.1 = true := mem_zeckIndices_iff_get_true x j.1 j.isLt
      _ ↔ x.1 j = true := by
            simp [Omega.get, j.isLt]
  cases hx : x.1 j <;> cases hy : (ofIndices m (zeckIndices x) (zeckIndices_isZeckendorfRep x)).1 j <;>
    simp [hx, hy] at hiff <;> rfl

@[simp] theorem zeckendorf_stableValue (x : X m) :
    Nat.zeckendorf (stableValue x) = zeckIndices x := by
  rw [stableValue_eq_sum_fib_zeckIndices]
  exact Nat.zeckendorf_sum_fib (zeckIndices_isZeckendorfRep x)

/-- The length-`m` stable prefix cut out from the Zeckendorf representation of a natural number. -/
def ofNat (m : Nat) (n : Nat) : X m :=
  ofIndices m (Nat.zeckendorf n) (Nat.isZeckendorfRep_zeckendorf n)

@[simp] theorem get_ofNat_eq_true_iff {i : Nat} (h : i < m) :
    get (ofNat m n).1 i = true ↔ i + 2 ∈ Nat.zeckendorf n :=
  get_ofIndices_eq_true_iff (m := m) (l := Nat.zeckendorf n) _ h

@[simp] theorem ofNat_stableValue (x : X m) :
    ofNat m (stableValue x) = x := by
  simpa [ofNat, zeckendorf_stableValue] using (ofIndices_zeckIndices x)

end X

/-- The paper's finite folding map: take the weighted value, normalize by Zeckendorf, then keep the
first `m` digits.
    def:fold-word -/
def Fold (w : Word m) : X m :=
  X.ofNat m (weight w)

@[simp] theorem get_Fold_eq_true_iff {w : Word m} {i : Nat} (h : i < m) :
    get (Fold w).1 i = true ↔ i + 2 ∈ Nat.zeckendorf (weight w) :=
  X.get_ofNat_eq_true_iff (m := m) (n := weight w) h

/-- Stable words are already in normal folded form.
    prop:fold-rewrite-newman -/
@[simp] theorem Fold_stable (x : X m) : Fold x.1 = x := by
  simpa [Fold, stableValue] using X.ofNat_stableValue x

/-- The finite folding map is idempotent.
    prop:fold-idempotent -/
@[simp] theorem Fold_idempotent (w : Word m) : Fold (Fold w).1 = Fold w :=
  Fold_stable (Fold w)

/-- The finite folding map is surjective onto the stable syntax space.
    prop:fold-basic -/
theorem Fold_surjective (m : Nat) : Function.Surjective (Fold (m := m)) := by
  intro x
  exact ⟨x.1, Fold_stable x⟩

end Omega
