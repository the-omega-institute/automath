import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Omega.Core.Fib
import Omega.Core.No11

namespace Omega

/-- The stable syntax space of length `m`. -/
def X (m : Nat) := { w : Word m // No11 w }

namespace X

noncomputable instance instFintype (m : Nat) : Fintype (X m) :=
  by
    classical
    letI : DecidablePred (fun w : Word m => No11 w) := Classical.decPred _
    delta X
    infer_instance

instance instFinite (m : Nat) : Finite (X m) :=
  Finite.of_fintype (X m)

/-- A stable word ends in `0` when its final accessible bit is `false`. -/
def EndsInZero (x : X m) : Prop :=
  get x.1 (m - 1) = false

/-- A stable word ends in `1` when its final accessible bit is `true`. -/
def EndsInOne (x : X m) : Prop :=
  get x.1 (m - 1) = true

noncomputable instance instFintypeEndsInZero (m : Nat) : Fintype {x : X m // EndsInZero x} := by
  classical
  infer_instance

noncomputable instance instFintypeEndsInOne (m : Nat) : Fintype {x : X m // EndsInOne x} := by
  classical
  infer_instance

/-- Forget the last bit of a stable word.
    engine:x-restrict -/
def restrict (x : X (m + 1)) : X m :=
  ⟨Omega.truncate x.1, no11_truncate x.2⟩

/-- Append `0` to the right of a stable word. -/
def appendFalse (x : X m) : X (m + 1) :=
  ⟨Omega.snoc x.1 false, no11_snoc_false x.2⟩

/-- Append `1` to the right of a stable word when the current last bit is `0`. -/
def appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) : X (m + 1) :=
  ⟨Omega.snoc x.1 true, no11_snoc_true x.2 hLast⟩

@[simp] theorem restrict_val (x : X (m + 1)) :
    (restrict x).1 = Omega.truncate x.1 := rfl

@[simp] theorem restrict_apply (x : X (m + 1)) (i : Fin m) :
    (restrict x).1 i = x.1 ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self m)⟩ := rfl

@[simp] theorem appendFalse_val (x : X m) :
    (appendFalse x).1 = Omega.snoc x.1 false := rfl

@[simp] theorem restrict_appendFalse (x : X m) : restrict (appendFalse x) = x := by
  apply Subtype.ext
  simp [appendFalse, restrict]

@[simp] theorem appendTrue_val (x : X m) (hLast : get x.1 (m - 1) = false) :
    (appendTrue x hLast).1 = Omega.snoc x.1 true := rfl

@[simp] theorem restrict_appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) :
    restrict (appendTrue x hLast) = x := by
  apply Subtype.ext
  simp [appendTrue, restrict]

theorem appendFalse_reconstruct (x : X (m + 1)) (hLast : Omega.last x.1 = false) :
    appendFalse (restrict x) = x := by
  apply Subtype.ext
  funext i
  by_cases hlt : i.1 < m
  · simp [appendFalse, restrict, Omega.truncate, Omega.snoc, hlt]
  · have hEq : i.1 = m := Nat.eq_of_lt_succ_of_not_lt i.isLt hlt
    have hFin : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hEq
    cases hFin
    simpa [appendFalse, restrict, Omega.last] using hLast

theorem appendTrue_reconstruct (x : X (m + 1))
    (hLast : Omega.last x.1 = true)
    (hRestrict : get (restrict x).1 (m - 1) = false) :
    appendTrue (restrict x) hRestrict = x := by
  apply Subtype.ext
  funext i
  by_cases hlt : i.1 < m
  · simp [appendTrue, restrict, Omega.truncate, Omega.snoc, hlt]
  · have hEq : i.1 = m := Nat.eq_of_lt_succ_of_not_lt i.isLt hlt
    have hFin : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hEq
    cases hFin
    simpa [appendTrue, restrict, Omega.last] using hLast

/-- The empty word is stable. -/
def empty : X 0 := by
  let w : Word 0 := fun i => False.elim (Nat.not_lt_zero _ i.isLt)
  refine ⟨w, ?_⟩
  intro i hi _
  exact Nat.not_lt_zero i (lt_of_get_eq_true hi)

instance : Unique (X 0) where
  default := empty
  uniq x := by
    apply Subtype.ext
    funext i
    exact False.elim (Nat.not_lt_zero _ i.isLt)

@[simp] theorem card_zero : Fintype.card (X 0) = 1 := by
  exact Fintype.card_unique (α := X 0)

@[simp] theorem endsInZero_zero (x : X 0) : EndsInZero x := by
  simp [EndsInZero, Omega.get]

@[simp] theorem not_endsInOne_zero (x : X 0) : ¬ EndsInOne x := by
  simp [EndsInOne, Omega.get]

theorem endsInZero_or_endsInOne (x : X m) : EndsInZero x ∨ EndsInOne x := by
  cases hBit : get x.1 (m - 1)
  · left
    simpa [EndsInZero] using hBit
  · right
    simpa [EndsInOne] using hBit

theorem endsInZero_not_endsInOne (x : X m) (hZero : EndsInZero x) : ¬ EndsInOne x := by
  intro hOne
  rw [EndsInZero] at hZero
  rw [EndsInOne] at hOne
  simp [hZero] at hOne

theorem restrict_endsInZero_of_last_true (x : X (m + 1)) (hLast : Omega.last x.1 = true) :
    EndsInZero (restrict x) := by
  dsimp [EndsInZero]
  cases m with
  | zero =>
      simp [Omega.get]
  | succ n =>
      have hLast' : get x.1 (n + 1) = true := by
        simpa [Omega.last, Omega.get] using hLast
      cases hPrev : get (restrict x).1 n with
      | false =>
          simpa [restrict, Omega.get] using hPrev
      | true =>
          have hPrevWord : get (Omega.truncate x.1) n = true := by
            simpa [restrict] using hPrev
          have hPrev' : get x.1 n = true := by
            rw [truncate_get_eq (w := x.1) (i := n) (h := Nat.lt_succ_self n)] at hPrevWord
            exact hPrevWord
          exact False.elim (x.2 n hPrev' hLast')

noncomputable def endsInCoverEquiv (m : Nat) :
    {x : X m // EndsInZero x ∨ EndsInOne x} ≃ X m where
  toFun x := x.1
  invFun x := ⟨x, endsInZero_or_endsInOne x⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := rfl

noncomputable def endsInOrEquivSum (m : Nat) :
    {x : X m // EndsInZero x ∨ EndsInOne x} ≃
      ({x : X m // EndsInZero x} ⊕ {x : X m // EndsInOne x}) where
  toFun x := by
    classical
    by_cases hZero : EndsInZero x.1
    · exact Sum.inl ⟨x.1, hZero⟩
    · exact Sum.inr ⟨x.1, by
        rcases x.2 with hZero' | hOne
        · exact False.elim (hZero hZero')
        · exact hOne⟩
  invFun
    | Sum.inl x => ⟨x.1, Or.inl x.2⟩
    | Sum.inr x => ⟨x.1, Or.inr x.2⟩
  left_inv x := by
    classical
    rcases x with ⟨x, hx⟩
    by_cases hZero : EndsInZero x
    · simp [hZero]
    · have hOne : EndsInOne x := by
        rcases hx with hZero' | hOne
        · exact False.elim (hZero hZero')
        · exact hOne
      simp [hZero]
  right_inv x := by
    classical
    cases x with
    | inl x =>
        have hZero : EndsInZero x.1 := x.2
        simp [hZero]
    | inr x =>
        have hZero : ¬ EndsInZero x.1 := by
          intro hx
          exact endsInZero_not_endsInOne x.1 hx x.2
        simp [hZero]

noncomputable def appendFalseEquivLastFalse (m : Nat) :
    X m ≃ {x : X (m + 1) // Omega.last x.1 = false} where
  toFun x := ⟨appendFalse x, by simp [Omega.last]⟩
  invFun x := restrict x.1
  left_inv x := by
    simp
  right_inv x := by
    apply Subtype.ext
    simpa using appendFalse_reconstruct x.1 x.2

noncomputable def appendTrueEquivLastTrue (m : Nat) :
    {x : X m // EndsInZero x} ≃ {x : X (m + 1) // Omega.last x.1 = true} where
  toFun x := ⟨appendTrue x.1 x.2, by simp [Omega.last]⟩
  invFun x := ⟨restrict x.1, restrict_endsInZero_of_last_true x.1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simpa using appendTrue_reconstruct x.1 x.2 (restrict_endsInZero_of_last_true x.1 x.2)

@[simp] theorem card_endsInZero_succ (m : Nat) :
    Fintype.card {x : X (m + 1) // EndsInZero x} = Fintype.card (X m) := by
  classical
  simpa [EndsInZero, Omega.last, Omega.get] using
    (Fintype.card_congr (appendFalseEquivLastFalse m)).symm

@[simp] theorem card_endsInOne_succ (m : Nat) :
    Fintype.card {x : X (m + 1) // EndsInOne x} =
      Fintype.card {x : X m // EndsInZero x} := by
  classical
  simpa [EndsInOne, EndsInZero, Omega.last, Omega.get] using
    (Fintype.card_congr (appendTrueEquivLastTrue m)).symm

theorem card_eq_endsInZero_add_endsInOne (m : Nat) :
    Fintype.card (X m) =
      Fintype.card {x : X m // EndsInZero x} +
      Fintype.card {x : X m // EndsInOne x} := by
  classical
  calc
    Fintype.card (X m)
      = Fintype.card {x : X m // EndsInZero x ∨ EndsInOne x} := by
          simpa using (Fintype.card_congr (endsInCoverEquiv m)).symm
    _ = Fintype.card ({x : X m // EndsInZero x} ⊕ {x : X m // EndsInOne x}) := by
          exact Fintype.card_congr (endsInOrEquivSum m)
    _ = Fintype.card {x : X m // EndsInZero x} +
          Fintype.card {x : X m // EndsInOne x} := by
          simp [Fintype.card_sum]

/-- prop:folding-stable-syntax-terminal-recursion -/
theorem card_recurrence (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) := by
  calc
    Fintype.card (X (m + 2))
      = Fintype.card {x : X (m + 2) // EndsInZero x} +
          Fintype.card {x : X (m + 2) // EndsInOne x} := card_eq_endsInZero_add_endsInOne (m + 2)
    _ = Fintype.card (X (m + 1)) + Fintype.card {x : X (m + 1) // EndsInZero x} := by
      rw [card_endsInZero_succ (m + 1), card_endsInOne_succ (m + 1)]
    _ = Fintype.card (X (m + 1)) + Fintype.card (X m) := by
      rw [card_endsInZero_succ m]

@[simp] theorem card_one : Fintype.card (X 1) = 2 := by
  calc
    Fintype.card (X 1)
      = Fintype.card {x : X 1 // EndsInZero x} + Fintype.card {x : X 1 // EndsInOne x} := by
          simpa using card_eq_endsInZero_add_endsInOne 1
    _ = Fintype.card (X 0) + Fintype.card {x : X 0 // EndsInZero x} := by
          rw [card_endsInZero_succ 0, card_endsInOne_succ 0]
    _ = 1 + 1 := by
          simp
    _ = 2 := by norm_num

/-- prop:folding-stable-syntax-fibonacci-count -/
theorem card_eq_fib : ∀ m : Nat, Fintype.card (X m) = Nat.fib (m + 2)
  | 0 => by simp
  | 1 => by exact card_one
  | m + 2 => by
      rw [card_recurrence, card_eq_fib (m + 1), card_eq_fib m]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (fib_succ_succ' (m + 2)).symm

/-- Number of stable words ending in 1 equals F(m).
    thm:card-X-ending-true -/
theorem card_endsInOne_eq_fib : ∀ (m : Nat), 1 ≤ m →
    Fintype.card {x : X m // EndsInOne x} = Nat.fib m
  | 1, _ => by
    classical
    rw [card_endsInOne_succ 0]
    simp [Nat.fib]
  | m + 2, _ => by
    classical
    rw [card_endsInOne_succ (m + 1), card_endsInZero_succ m, card_eq_fib m]

/-- The cardinality of X_m words with last bit true equals F(m), expressed as a Finset filter.
    thm:card-X-ending-true-filter -/
theorem card_X_endingTrue (m : Nat) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun w : X m => w.1 ⟨m - 1, by omega⟩ = true)).card
    = Nat.fib m := by
  classical
  rw [← card_endsInOne_eq_fib m hm]
  rw [Fintype.card_subtype]
  congr 1
  ext w
  simp only [EndsInOne, Omega.get, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlt : m - 1 < m := by omega
  rw [dif_pos hlt]

end X

end Omega
