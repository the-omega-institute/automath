import Mathlib.Data.Nat.Fib.Zeckendorf
import Omega.Folding.Value

namespace Omega

/-- Project-level name for mathlib's Zeckendorf representation type. -/
abbrev ZeckendorfRep := {l : List Nat // l.IsZeckendorfRep}

/-- Project-level alias for mathlib's Zeckendorf equivalence.
    bridge:mathlib-zeckendorf-equiv -/
abbrev natZeckendorfEquiv : Nat ≃ ZeckendorfRep := Nat.zeckendorfEquiv

@[simp] theorem sum_nat_zeckendorf_fib (n : Nat) :
    ((Nat.zeckendorf n).map Nat.fib).sum = n := by
  exact Nat.sum_zeckendorf_fib n


namespace X

/-- The descending list of active Fibonacci indices carried by a stable word. -/
def zeckIndices : {m : Nat} → X m → List Nat
  | 0, _ => []
  | m + 1, x =>
      if Omega.last x.1 = true then
        (m + 2) :: zeckIndices (restrict x)
      else
        zeckIndices (restrict x)

@[simp] theorem zeckIndices_empty : zeckIndices empty = [] := rfl

@[simp] theorem zeckIndices_appendFalse (x : X m) :
    zeckIndices (appendFalse x) = zeckIndices x := by
  simp [zeckIndices, Omega.last]

@[simp] theorem zeckIndices_appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) :
    zeckIndices (appendTrue x hLast) = (m + 2) :: zeckIndices x := by
  simp [zeckIndices, Omega.last]

theorem mem_zeckIndices_lt : ∀ {m : Nat} (x : X m) {a : Nat},
    a ∈ zeckIndices x → a < m + 2
  | 0, x, _a, ha => by
      have hx : x = empty := Subsingleton.elim _ _
      subst hx
      simp [zeckIndices] at ha
  | m + 1, x, a, ha => by
      by_cases hLast : Omega.last x.1 = true
      · simp [zeckIndices, hLast] at ha
        rcases ha with rfl | ha
        · exact Nat.lt_succ_self (m + 2)
        · exact Nat.lt_trans (mem_zeckIndices_lt (restrict x) ha) (Nat.lt_succ_self _)
      · have hLastFalse : Omega.last x.1 = false := by
          cases hBit : Omega.last x.1 <;> simp [hBit] at hLast ⊢
        simp [zeckIndices, hLastFalse] at ha
        exact Nat.lt_trans (mem_zeckIndices_lt (restrict x) ha) (Nat.lt_succ_self _)

theorem head_zeckIndices_append_zero_lt_of_endsInZero :
    ∀ {m : Nat} (x : X m) (_ : EndsInZero x) {a : Nat},
      a ∈ (zeckIndices x ++ [0]).head? → a < m + 1
  | 0, x, _hZero, a, ha => by
      have hx : x = empty := Subsingleton.elim _ _
      subst hx
      simp [zeckIndices] at ha
      subst a
      simp
  | m + 1, x, hZero, a, ha => by
      have hLast : Omega.last x.1 = false := by
        simpa [EndsInZero, Omega.last, Omega.get] using hZero
      have hEq : zeckIndices x = zeckIndices (restrict x) := by
        simp [zeckIndices, hLast]
      rw [hEq] at ha
      cases hTail : zeckIndices (restrict x) with
      | nil =>
          simp [hTail] at ha
          subst a
          exact Nat.succ_pos _
      | cons b l =>
          simp [hTail] at ha
          subst a
          have hb : b ∈ zeckIndices (restrict x) := by simp [hTail]
          exact mem_zeckIndices_lt (restrict x) hb

/-- bridge:stable-word-is-zeckendorf-rep -/
theorem zeckIndices_isZeckendorfRep : ∀ {m : Nat} (x : X m),
    (zeckIndices x).IsZeckendorfRep
  | 0, _x => by
      simp [zeckIndices, List.IsZeckendorfRep]
  | m + 1, x => by
      by_cases hLast : Omega.last x.1 = true
      · have hRestrict : EndsInZero (restrict x) := restrict_endsInZero_of_last_true x hLast
        simp [zeckIndices, hLast, List.IsZeckendorfRep, List.cons_append]
        refine (zeckIndices_isZeckendorfRep (restrict x)).cons (fun a ha => ?_)
        have haLt : a < m + 1 :=
          head_zeckIndices_append_zero_lt_of_endsInZero (restrict x) hRestrict ha
        simpa [Nat.add_assoc] using Nat.add_le_add_right (Nat.succ_le_of_lt haLt) 1
      · have hLastFalse : Omega.last x.1 = false := by
          cases hBit : Omega.last x.1 <;> simp [hBit] at hLast ⊢
        simpa [zeckIndices, hLastFalse] using zeckIndices_isZeckendorfRep (restrict x)

/-- The Zeckendorf representation encoded by a stable word. -/
def zeckRep (x : X m) : ZeckendorfRep :=
  ⟨zeckIndices x, zeckIndices_isZeckendorfRep x⟩

/-- The stable value is the sum of the active Fibonacci indices.
    bridge:stable-value-zeck-indices -/
theorem stableValue_eq_sum_fib_zeckIndices : ∀ {m : Nat} (x : X m),
    stableValue x = ((zeckIndices x).map Nat.fib).sum
  | 0, x => by
      have hx : x = empty := by
        exact Subsingleton.elim _ _
      subst hx
      simp [stableValue, zeckIndices, weight]
  | m + 1, x => by
      by_cases hLast : Omega.last x.1 = true
      · have hRestrict : EndsInZero (restrict x) := restrict_endsInZero_of_last_true x hLast
        calc
          stableValue x = stableValue (appendTrue (restrict x) hRestrict) := by
            simpa using congrArg stableValue (appendTrue_reconstruct x hLast hRestrict).symm
          _ = stableValue (restrict x) + Nat.fib (m + 2) := by
            exact stableValue_appendTrue (restrict x) hRestrict
          _ = ((zeckIndices (restrict x)).map Nat.fib).sum + Nat.fib (m + 2) := by
            rw [stableValue_eq_sum_fib_zeckIndices (restrict x)]
          _ = Nat.fib (m + 2) + ((zeckIndices (restrict x)).map Nat.fib).sum := by
            rw [add_comm]
          _ = (((m + 2) :: zeckIndices (restrict x)).map Nat.fib).sum := by
            simp
          _ = ((zeckIndices x).map Nat.fib).sum := by
            simp [zeckIndices, hLast]
      · have hLastFalse : Omega.last x.1 = false := by
          cases hBit : Omega.last x.1 <;> simp [hBit] at hLast ⊢
        calc
          stableValue x = stableValue (appendFalse (restrict x)) := by
            simpa using congrArg stableValue (appendFalse_reconstruct x hLastFalse).symm
          _ = stableValue (restrict x) := by
            exact stableValue_restrict_appendFalse (restrict x)
          _ = ((zeckIndices (restrict x)).map Nat.fib).sum :=
            stableValue_eq_sum_fib_zeckIndices (restrict x)
          _ = ((zeckIndices x).map Nat.fib).sum := by
            simp [zeckIndices, hLast]

@[simp] theorem sum_fib_zeckRep (x : X m) :
    ((zeckRep x).1.map Nat.fib).sum = stableValue x := by
  simpa [zeckRep] using (stableValue_eq_sum_fib_zeckIndices x).symm

/-- The zeckIndices list has length ≤ m. -/
theorem zeckIndices_length_le (x : X m) :
    (zeckIndices x).length ≤ m := by
  induction m with
  | zero =>
    have : x = empty := Subsingleton.elim _ _
    subst this; simp [zeckIndices]
  | succ n ih =>
    by_cases hLast : Omega.last x.1 = true
    · simp [zeckIndices, hLast, ih (restrict x)]
    · have hFalse : Omega.last x.1 = false := by
        cases h : Omega.last x.1 <;> simp_all
      simp only [zeckIndices, hFalse]
      exact Nat.le_succ_of_le (ih (restrict x))

/-- The Zeckendorf representation determines the stable value. -/
theorem stableValue_eq_of_zeckIndices_eq {x y : X m} (h : zeckIndices x = zeckIndices y) :
    stableValue x = stableValue y := by
  rw [stableValue_eq_sum_fib_zeckIndices x, stableValue_eq_sum_fib_zeckIndices y, h]

/-- The all-false stable word has empty Zeckendorf indices.
    lem:zeckIndices-allFalse -/
@[simp] theorem zeckIndices_allFalse :
    zeckIndices (⟨fun _ => false, no11_allFalse⟩ : X m) = [] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [zeckIndices, Omega.last, Bool.false_eq_true, ↓reduceIte]
    convert ih using 2

end X

end Omega
