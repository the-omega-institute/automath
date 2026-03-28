namespace Omega

/-- A fixed-length binary word. -/
abbrev Word (m : Nat) := Fin m → Bool

/-- Access a word by a natural index, returning `false` out of range. -/
def get (w : Word m) (i : Nat) : Bool :=
  if h : i < m then
    w ⟨i, h⟩
  else
    false

/-- Drop the last coordinate of a length-`m+1` word. -/
def truncate (w : Word (m + 1)) : Word m :=
  fun i => w ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self m)⟩

/-- Append one bit to the right of a word. -/
def snoc (w : Word m) (b : Bool) : Word (m + 1) :=
  fun i =>
    if h : i.1 < m then
      w ⟨i.1, h⟩
    else
      b

/-- The last bit of a nonempty word. -/
def last (w : Word (m + 1)) : Bool :=
  w ⟨m, Nat.lt_succ_self m⟩

@[simp] theorem get_of_lt (w : Word m) {i : Nat} (h : i < m) :
    get w i = w ⟨i, h⟩ := by
  simp [get, h]

@[simp] theorem get_of_not_lt (w : Word m) {i : Nat} (h : ¬ i < m) :
    get w i = false := by
  simp [get, h]

theorem lt_of_get_eq_true {w : Word m} {i : Nat} (h : get w i = true) : i < m := by
  by_cases hi : i < m
  · exact hi
  · simp [get, hi] at h

theorem lt_of_get_eq_true_succ {w : Word m} {i : Nat} (h : get w (i + 1) = true) : i + 1 < m :=
  lt_of_get_eq_true h

@[simp] theorem truncate_get_eq (w : Word (m + 1)) {i : Nat} (h : i < m) :
    get (truncate w) i = get w i := by
  have hs : i < m + 1 := Nat.lt_trans h (Nat.lt_succ_self m)
  simp [get, truncate, h, hs]

@[simp] theorem truncate_get_of_ge (w : Word (m + 1)) {i : Nat} (h : m ≤ i) :
    get (truncate w) i = false := by
  simp [get, Nat.not_lt.mpr h]

@[simp] theorem truncate_snoc (w : Word m) (b : Bool) : truncate (snoc w b) = w := by
  funext i
  simp [truncate, snoc, i.isLt]

@[simp] theorem snoc_last (w : Word m) (b : Bool) :
    snoc w b ⟨m, Nat.lt_succ_self m⟩ = b := by
  simp [snoc]

@[simp] theorem last_snoc (w : Word m) (b : Bool) : last (snoc w b) = b := by
  simp [last, snoc]

@[simp] theorem snoc_get_eq (w : Word m) (b : Bool) {i : Nat} (h : i < m) :
    get (snoc w b) i = get w i := by
  have hs : i < m + 1 := Nat.lt_trans h (Nat.lt_succ_self m)
  simp [get, snoc, h, hs]

@[simp] theorem snoc_get_last_eq (w : Word m) (b : Bool) :
    get (snoc w b) m = b := by
  have hm : m < m + 1 := Nat.lt_succ_self m
  have hnot : ¬ m < m := Nat.not_lt.mpr (Nat.le_refl m)
  simp [get, snoc, hm, hnot]

@[simp] theorem snoc_get_false_of_ge (w : Word m) {i : Nat} (h : m ≤ i) :
    get (snoc w false) i = false := by
  by_cases hi : i < m + 1
  · have hnot : ¬ i < m := Nat.not_lt.mpr h
    simp [get, snoc, hi, hnot]
  · simp [get, hi]

@[simp] theorem snoc_get_of_gt (w : Word m) (b : Bool) {i : Nat} (h : m + 1 ≤ i) :
    get (snoc w b) i = false := by
  simp [get, Nat.not_lt.mpr h]

end Omega
