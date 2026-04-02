import Omega.Folding.Weight

namespace Omega

/-- The Fibonacci-weighted value restricted to stable words.
    def:val-on-D -/
def stableValue (x : X m) : Nat :=
  weight x.1

@[simp] theorem stableValue_restrict_appendFalse (x : X m) :
    stableValue (X.appendFalse x) = stableValue x := by
  simp [stableValue]

@[simp] theorem stableValue_appendTrue (x : X m) (hLast : get x.1 (m - 1) = false) :
    stableValue (X.appendTrue x hLast) = stableValue x + Nat.fib (m + 2) := by
  simp [stableValue, X.appendTrue, weight_snoc]

/-- Stable values are strictly bounded by the Fibonacci cardinality.
    This is the key bound enabling finite stable arithmetic on `X m`. -/
theorem stableValue_lt_fib : ∀ {m : Nat}, (x : X m) → stableValue x < Nat.fib (m + 2)
  | 0, x => by
    have : x = X.empty := Unique.eq_default x; subst this
    exact fib_succ_pos 1
  | n + 1, x => by
    by_cases hLast : Omega.last x.1 = true
    · -- x ends in true: stableValue x = stableValue(restrict x) + F(n+2)
      have hRestr : get (X.restrict x).1 (n - 1) = false :=
        X.restrict_endsInZero_of_last_true x hLast
      have hRec : X.appendTrue (X.restrict x) hRestr = x :=
        X.appendTrue_reconstruct x hLast hRestr
      rw [← hRec, stableValue_appendTrue]
      -- Need: stableValue(restrict x) < F(n+1)
      suffices h : stableValue (X.restrict x) < Nat.fib (n + 1) by
        calc stableValue (X.restrict x) + Nat.fib (n + 2)
            < Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.add_lt_add_right h _
          _ = Nat.fib (n + 2) + Nat.fib (n + 1) := Nat.add_comm _ _
          _ = Nat.fib (n + 3) := (fib_succ_succ' (n + 1)).symm
      cases n with
      | zero =>
        have : X.restrict x = X.empty := Unique.eq_default _
        rw [this]; exact fib_succ_pos 0
      | succ k =>
        have hRestrLast : Omega.last (X.restrict x).1 = false := by
          simp only [Omega.last, X.restrict_val, Omega.truncate]
          simp only [ Omega.get] at hRestr
          convert hRestr using 1
          simp
        have hRec2 := X.appendFalse_reconstruct (X.restrict x) hRestrLast
        rw [← hRec2, stableValue_restrict_appendFalse]
        exact stableValue_lt_fib (X.restrict (X.restrict x))
    · -- x ends in false: stableValue x = stableValue(restrict x) < F(n+2) ≤ F(n+3)
      have hLastFalse : Omega.last x.1 = false := by
        cases hBit : Omega.last x.1 <;> simp_all
      rw [← X.appendFalse_reconstruct x hLastFalse, stableValue_restrict_appendFalse]
      exact Nat.lt_of_lt_of_le
        (stableValue_lt_fib (X.restrict x))
        (Nat.fib_mono (by omega))



/-- The stable value decomposes as: restrict's value + last bit contribution. -/
theorem stableValue_eq_restrict_add_last (x : X (m + 1)) :
    stableValue x = stableValue (X.restrict x) +
      (if x.1 ⟨m, Nat.lt_succ_self m⟩ = true then Nat.fib (m + 2) else 0) := by
  simp [stableValue, weight, X.restrict]

/-- The stable value of restrict x is at most stableValue x. -/
theorem stableValue_restrict_le (x : X (m + 1)) :
    stableValue (X.restrict x) ≤ stableValue x := by
  rw [stableValue_eq_restrict_add_last]
  exact Nat.le_add_right _ _

/-- The stable value of restrict x equals stableValue x modulo F(m+2). -/
theorem stableValue_restrict_mod (x : X (m + 1)) :
    stableValue x % Nat.fib (m + 2) = stableValue (X.restrict x) % Nat.fib (m + 2) := by
  rw [stableValue_eq_restrict_add_last x]
  by_cases hLast : x.1 ⟨m, Nat.lt_succ_self m⟩ = true
  · simp only [hLast, ite_true, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  · have hFalse : x.1 ⟨m, Nat.lt_succ_self m⟩ = false := by
      cases h : x.1 ⟨m, _⟩ <;> simp_all
    simp only [hFalse, Bool.false_eq_true, ite_false, Nat.add_zero]

/-- The carry indicator for stable addition at resolution m+1.
    def:pom-carry-interference-graph -/
def carryIndicator (x y : X (m + 1)) : Nat :=
  if stableValue x + stableValue y ≥ Nat.fib (m + 3) then 1 else 0

/-- The carry indicator is zero when the sum is below the threshold. -/
theorem carryIndicator_zero_of_lt (x y : X (m + 1))
    (h : stableValue x + stableValue y < Nat.fib (m + 3)) :
    carryIndicator x y = 0 := by
  unfold carryIndicator; split_ifs with hge
  · omega
  · rfl

/-- The carry indicator is one when the sum reaches the threshold. -/
theorem carryIndicator_one_of_ge (x y : X (m + 1))
    (h : stableValue x + stableValue y ≥ Nat.fib (m + 3)) :
    carryIndicator x y = 1 :=
  if_pos h

/-- stableValue of the empty word is 0. -/
@[simp] theorem stableValue_empty : stableValue (X.empty : X 0) = 0 := by
  simp [stableValue, weight]

/-- stableValue is nonneg (trivially, since it's a Nat). -/
theorem stableValue_nonneg (x : X m) : 0 ≤ stableValue x :=
  Nat.zero_le _

/-- stableValue of the all-false stable word is 0.
    lem:stableValue-allFalse -/
@[simp] theorem stableValue_allFalse :
    stableValue (⟨fun _ => false, no11_allFalse⟩ : X m) = 0 := by
  simp [stableValue, weight_allFalse]

/-- stableValue equals weight of the underlying word.
    lem:stableValue-eq-weight -/
theorem stableValue_eq_weight (x : X m) : stableValue x = weight x.1 := rfl


-- ══════════════════════════════════════════════════════════════
-- Phase 204: stableValue injectivity
-- ══════════════════════════════════════════════════════════════

/-- stableValue is injective on X m: distinct stable words have distinct values.
    thm:fold-zeckendorf-mod-decomposition-unique -/
theorem stableValue_injective (m : Nat) : Function.Injective (fun x : X m => stableValue x) := by
  intro x y hval
  -- Simplify: (fun x => stableValue x) a = ... → stableValue a = ...
  simp only at hval
  induction m with
  | zero =>
    exact Subtype.ext (funext (fun i => (Nat.not_lt_zero i.1 i.2).elim))
  | succ n ih =>
    -- Decompose both values using last-bit split
    have hx := stableValue_eq_restrict_add_last x
    have hy := stableValue_eq_restrict_add_last y
    -- Case split on last bits of x and y
    by_cases hxlast : x.1 ⟨n, Nat.lt_succ_self n⟩ = true <;>
    by_cases hylast : y.1 ⟨n, Nat.lt_succ_self n⟩ = true
    · -- Both end in true: restrict values must be equal
      simp only [hxlast, hylast, ite_true] at hx hy
      have hrestr : stableValue (X.restrict x) = stableValue (X.restrict y) := by omega
      have hreq := ih hrestr
      -- Reconstruct: x and y have same restrict and same last bit
      exact Subtype.ext (funext fun i => by
        by_cases hi : i.1 < n
        · -- For indices < n: use restrict equality
          have h1 : (X.restrict x).1 ⟨i.1, hi⟩ = (X.restrict y).1 ⟨i.1, hi⟩ :=
            congr_arg (fun z => z.1 ⟨i.1, hi⟩) hreq
          simp [X.restrict] at h1; exact h1
        · have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.2 hi)
          subst this; rw [hxlast, hylast])
    · -- x ends in true, y ends in false: value range contradiction
      simp only [hxlast, ite_true, hylast, Bool.false_eq_true, ite_false] at hx hy
      have hyr : stableValue (X.restrict y) < Nat.fib (n + 2) :=
        stableValue_lt_fib (X.restrict y)
      omega
    · -- x ends in false, y ends in true: symmetric contradiction
      simp only [hxlast, Bool.false_eq_true, ite_false, hylast, ite_true] at hx hy
      have hxr : stableValue (X.restrict x) < Nat.fib (n + 2) :=
        stableValue_lt_fib (X.restrict x)
      omega
    · -- Both end in false: restrict values must be equal
      simp only [hxlast, hylast, Bool.false_eq_true, ite_false] at hx hy
      have hrestr : stableValue (X.restrict x) = stableValue (X.restrict y) := by omega
      have hreq := ih hrestr
      exact Subtype.ext (funext fun i => by
        by_cases hi : i.1 < n
        · have h1 : (X.restrict x).1 ⟨i.1, hi⟩ = (X.restrict y).1 ⟨i.1, hi⟩ :=
            congr_arg (fun z => z.1 ⟨i.1, hi⟩) hreq
          simp [X.restrict] at h1; exact h1
        · have : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.2 hi)
          subst this
          have hxf : x.1 ⟨n, Nat.lt_succ_self n⟩ = false := by
            cases h : x.1 ⟨n, _⟩ <;> simp_all
          have hyf : y.1 ⟨n, Nat.lt_succ_self n⟩ = false := by
            cases h : y.1 ⟨n, _⟩ <;> simp_all
          rw [hxf, hyf])

end Omega
