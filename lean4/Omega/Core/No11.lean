import Omega.Core.Word

namespace Omega

/-- A binary word with no adjacent `true true` pattern. -/
def No11 (w : Word m) : Prop :=
  ∀ i : Nat, get w i = true → get w (i + 1) = true → False

/-- engine:no11-truncate -/
@[simp] theorem no11_truncate {w : Word (m + 1)} (h : No11 w) : No11 (truncate w) := by
  intro i hi hi1
  have hiLt : i < m := lt_of_get_eq_true hi
  have hi1Lt : i + 1 < m := lt_of_get_eq_true_succ hi1
  have hi' : get w i = true := by
    simpa [truncate_get_eq w hiLt] using hi
  have hi1' : get w (i + 1) = true := by
    simpa [truncate_get_eq w hi1Lt] using hi1
  exact h i hi' hi1'

@[simp] theorem no11_snoc_false {w : Word m} (h : No11 w) : No11 (snoc w false) := by
  intro i hi hi1
  by_cases hs : i + 1 < m
  · have hiLt : i < m := Nat.lt_of_succ_lt hs
    have hi' : get w i = true := by
      simpa [snoc_get_eq w false hiLt] using hi
    have hi1' : get w (i + 1) = true := by
      simpa [snoc_get_eq w false hs] using hi1
    exact h i hi' hi1'
  · have hm : m ≤ i + 1 := Nat.not_lt.mp hs
    rw [snoc_get_false_of_ge w hm] at hi1
    cases hi1

@[simp] theorem no11_snoc_true {w : Word m} (h : No11 w) (hLast : get w (m - 1) = false) :
    No11 (snoc w true) := by
  intro i hi hi1
  by_cases hs : i + 1 < m
  · have hiLt : i < m := Nat.lt_of_succ_lt hs
    have hi' : get w i = true := by
      simpa [snoc_get_eq w true hiLt] using hi
    have hi1' : get w (i + 1) = true := by
      simpa [snoc_get_eq w true hs] using hi1
    exact h i hi' hi1'
  · have hm : m ≤ i + 1 := Nat.not_lt.mp hs
    have hi1Le : i + 1 ≤ m := Nat.lt_succ_iff.mp (lt_of_get_eq_true hi1)
    have hEq : i + 1 = m := Nat.le_antisymm hi1Le hm
    have hiLt : i < m := by
      simpa [hEq] using Nat.lt_succ_self i
    have hi' : get w i = true := by
      simpa [snoc_get_eq w true hiLt] using hi
    have hiIndex : i = m - 1 := Nat.eq_sub_of_add_eq hEq
    have hiLast : get w (m - 1) = true := by
      simpa [hiIndex] using hi'
    rw [hLast] at hiLast
    cases hiLast

/-- The all-false word satisfies No11. -/
theorem no11_allFalse : No11 (fun _ : Fin m => false) := by
  intro i hi
  simp only [get, dite_eq_ite] at hi
  split at hi
  · simp at hi
  · simp at hi

/-- No11 is closed under truncation (named). -/
theorem no11_of_truncate {w : Word (m + 1)} (h : No11 w) : No11 (truncate w) :=
  no11_truncate h

/-- No11 is closed under appending false (named). -/
theorem no11_append_false {w : Word m} (h : No11 w) : No11 (snoc w false) :=
  no11_snoc_false h

/-- No11 is closed under appending true when the last bit is false. -/
theorem no11_append_true {w : Word m} (h : No11 w) (hLast : get w (m - 1) = false) :
    No11 (snoc w true) :=
  no11_snoc_true h hLast



-- ══════════════════════════════════════════════════════════════
-- Phase 220: Word reversal + No11 preservation
-- ══════════════════════════════════════════════════════════════

/-- Index reversal of a word: wordReverse w maps position i to w[m-1-i].
    thm:pom-fibcube-aut-z2 -/
def wordReverse (w : Word m) : Word m :=
  fun i => w ⟨m - 1 - i.val, by omega⟩

/-- Index reversal preserves No11. thm:pom-fibcube-aut-z2 -/
theorem no11_reverse {w : Word m} (hw : No11 w) : No11 (wordReverse w) := by
  intro k hk hk1
  have hkLt : k < m := lt_of_get_eq_true hk
  have hk1Lt : k + 1 < m := lt_of_get_eq_true hk1
  -- Use No11 on w at position (m-2-k): w[m-2-k] and w[m-1-k] both true
  -- From hk1: get (wordReverse w) (k+1) = w[m-1-(k+1)] = w[m-2-k] = true
  -- From hk:  get (wordReverse w) k     = w[m-1-k]           = true
  apply hw (m - 2 - k)
  · -- get w (m-2-k) = true
    show get w (m - 2 - k) = true
    have hlt : m - 2 - k < m := by omega
    rw [get_of_lt _ hlt]
    rw [get_of_lt _ hk1Lt] at hk1
    simp only [wordReverse] at hk1
    have : (⟨m - 1 - (k + 1), by omega⟩ : Fin m) = ⟨m - 2 - k, hlt⟩ := by
      apply Fin.ext; simp; omega
    rw [this] at hk1; exact hk1
  · -- get w (m-2-k+1) = get w (m-1-k) = true
    show get w (m - 2 - k + 1) = true
    have heq : m - 2 - k + 1 = m - 1 - k := by omega
    have hlt2 : m - 1 - k < m := by omega
    rw [heq, get_of_lt _ hlt2]
    rw [get_of_lt _ hkLt] at hk
    simp only [wordReverse] at hk; exact hk

-- ══════════════════════════════════════════════════════════════
-- Phase R133: All-true word not stable
-- ══════════════════════════════════════════════════════════════

/-- The all-true word is not stable for m ≥ 2 (contains adjacent 11).
    prop:fold-basic -/
theorem allTrue_not_no11 (hm : 2 ≤ m) : ¬ No11 (fun _ : Fin m => true) := by
  intro h
  have h0 : get (fun _ : Fin m => true) 0 = true := by simp [get, show (0 : Nat) < m from by omega]
  have h1 : get (fun _ : Fin m => true) 1 = true := by simp [get, show (1 : Nat) < m from by omega]
  exact h 0 h0 h1

/-- Paper: prop:fold-basic (all-ones forbidden) -/
theorem paper_allTrue_not_no11 (hm : 2 ≤ m) : ¬ No11 (fun _ : Fin m => true) :=
  allTrue_not_no11 hm

end Omega
