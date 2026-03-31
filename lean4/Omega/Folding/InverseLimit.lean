import Omega.Folding.Fold
import Omega.Folding.Value

namespace Omega

namespace X

/-- Infinite stable words with no adjacent `true true` pattern. -/
def No11Inf (a : Nat → Bool) : Prop :=
  ∀ i : Nat, ¬ (a i = true ∧ a (i + 1) = true)

/-- The inverse-limit carrier of finite stable syntax spaces. -/
abbrev XInfinity := {a : Nat → Bool // No11Inf a}

/-- The length-`m` prefix cut from an infinite stable word. -/
def prefixWord (a : XInfinity) (m : Nat) : X m := by
  refine ⟨fun i => a.1 i.1, ?_⟩
  intro i hi hi1
  have hiLt : i < m := lt_of_get_eq_true hi
  have hi1Lt : i + 1 < m := lt_of_get_eq_true_succ hi1
  have h0 : a.1 i = true := by
    simpa [Omega.get, hiLt] using hi
  have h1 : a.1 (i + 1) = true := by
    simpa [Omega.get, hi1Lt] using hi1
  exact a.2 i ⟨h0, h1⟩

@[simp] theorem prefixWord_val (a : XInfinity) :
    (prefixWord a m).1 = fun i => a.1 i.1 := rfl

@[simp] theorem prefixWord_last (a : XInfinity) :
    Omega.last (prefixWord a (m + 1)).1 = a.1 m := by
  rfl

@[simp] theorem restrict_prefixWord (a : XInfinity) :
    restrict (prefixWord a (m + 1)) = prefixWord a m := by
  apply Subtype.ext
  funext i
  rfl

/-- A compatible family in the inverse system `(X m, restrict)`. -/
structure CompatibleFamily where
  seq : ∀ m : Nat, X m
  compat : ∀ m : Nat, restrict (seq (m + 1)) = seq m

/-- The inverse-limit family induced by an infinite stable word. -/
def toFamily (a : XInfinity) : CompatibleFamily where
  seq := prefixWord a
  compat := fun m => restrict_prefixWord (m := m) a

/-- The distinguished bit read from resolution `m+1`. -/
def CompatibleFamily.bit (F : CompatibleFamily) (m : Nat) : Bool :=
  Omega.last (F.seq (m + 1)).1

@[simp] theorem bit_eq_last (F : CompatibleFamily) (m : Nat) :
    F.bit m = Omega.last (F.seq (m + 1)).1 := rfl

@[simp] theorem last_truncate (w : Word (m + 2)) :
    Omega.last (Omega.truncate w) = get w m := by
  simp [Omega.last, Omega.get, Omega.truncate]

/-- Recover an infinite stable word from a compatible family. -/
def ofFamily (F : CompatibleFamily) : XInfinity := by
  refine ⟨F.bit, ?_⟩
  intro i hPair
  have hi : F.bit i = true := hPair.1
  have hi1 : F.bit (i + 1) = true := hPair.2
  have hCompat : (restrict (F.seq (i + 2))).1 = (F.seq (i + 1)).1 :=
    congrArg Subtype.val (F.compat (i + 1))
  have hLeft : get (F.seq (i + 2)).1 i = true := by
    have hLastRestrict : Omega.last (restrict (F.seq (i + 2))).1 = true := by
      rw [hCompat]
      simpa [CompatibleFamily.bit] using hi
    simpa [X.restrict, last_truncate] using hLastRestrict
  have hRight : get (F.seq (i + 2)).1 (i + 1) = true := by
    simpa [CompatibleFamily.bit, Omega.last, Omega.get] using hi1
  exact (F.seq (i + 2)).2 i hLeft hRight

@[simp] theorem ofFamily_apply (F : CompatibleFamily) :
    (ofFamily F).1 m = F.bit m := rfl

/-- Two stable words of length `m+1` agree if their restrictions and last bits agree. -/
theorem eq_of_restrict_eq_last_eq {x y : X (m + 1)}
    (hRestrict : restrict x = restrict y)
    (hLast : Omega.last x.1 = Omega.last y.1) :
    x = y := by
  apply Subtype.ext
  funext i
  by_cases hi : i.1 < m
  · let j : Fin m := ⟨i.1, hi⟩
    have hWords : (restrict x).1 = (restrict y).1 := congrArg Subtype.val hRestrict
    have hEval : (restrict x).1 j = (restrict y).1 j := by
      simpa using congrArg (fun w => w j) hWords
    simpa [restrict] using hEval
  · have hEq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext (Nat.eq_of_lt_succ_of_not_lt i.isLt hi)
    cases hEq
    simpa [Omega.last] using hLast

@[simp] theorem ofFamily_toFamily (a : XInfinity) : ofFamily (toFamily a) = a := by
  apply Subtype.ext
  funext i
  simp [ofFamily, toFamily, CompatibleFamily.bit, prefixWord, Omega.last]

@[simp] theorem toFamily_ofFamily_seq :
    ∀ (F : CompatibleFamily) (m : Nat), (toFamily (ofFamily F)).seq m = F.seq m
  | F, 0 => by
      exact Subsingleton.elim _ _
  | F, m + 1 => by
      apply eq_of_restrict_eq_last_eq
      · calc
          restrict ((toFamily (ofFamily F)).seq (m + 1))
              = (toFamily (ofFamily F)).seq m := by
                  simp [toFamily]
          _ = F.seq m := toFamily_ofFamily_seq F m
          _ = restrict (F.seq (m + 1)) := by
                  symm
                  exact F.compat m
      · rfl

@[simp] theorem toFamily_ofFamily (F : CompatibleFamily) :
    toFamily (ofFamily F) = F := by
  cases F with
  | mk seq compat =>
      cases hG : toFamily (ofFamily { seq := seq, compat := compat }) with
      | mk seq' compat' =>
          have hseq : seq' = seq := by
            funext m
            simpa [hG] using toFamily_ofFamily_seq { seq := seq, compat := compat } m
          cases hseq
          have hcompat : compat' = compat := Subsingleton.elim _ _
          cases hcompat
          rfl

/-- The concrete inverse-limit equivalence used by the project.
    thm:inverse-limit-golden -/
def inverseLimitEquiv : CompatibleFamily ≃ XInfinity where
  toFun := ofFamily
  invFun := toFamily
  left_inv := toFamily_ofFamily
  right_inv := ofFamily_toFamily

/-- Infinite stable words are uniquely determined by their finite prefixes. -/
theorem XInfinity_ext {a b : XInfinity} (h : ∀ m, prefixWord a m = prefixWord b m) :
    a = b := by
  apply Subtype.ext
  funext i
  have := congr_arg (fun x => x.1 ⟨i, Nat.lt_succ_self i⟩) (h (i + 1))
  simpa [prefixWord] using this

/-- Compatible families are uniquely determined by their sequence. -/
theorem CompatibleFamily.ext {F G : CompatibleFamily} (h : ∀ m, F.seq m = G.seq m) :
    F = G := by
  have : F.seq = G.seq := funext h
  rcases F with ⟨seqF, compatF⟩
  rcases G with ⟨seqG, compatG⟩
  subst this
  rfl

/-- The prefix word at resolution m is determined by the first m bits. -/
theorem prefixWord_apply (a : XInfinity) (m : Nat) (i : Fin m) :
    (prefixWord a m).1 i = a.1 i.1 := rfl

/-- Two infinite stable words agree on all prefixes iff they are equal (extensionality, named). -/
theorem XInfinity_eq_iff (a b : XInfinity) :
    a = b ↔ ∀ m, prefixWord a m = prefixWord b m :=
  ⟨fun h => by rw [h]; intro _; rfl, XInfinity_ext⟩

/-- The inverse limit is a concrete realization of the projective limit
    of the system (X_m, restrict). -/
theorem inverseLimitEquiv_left_inv (F : CompatibleFamily) :
    toFamily (ofFamily F) = F :=
  toFamily_ofFamily F

/-- The inverse limit is a concrete realization of the projective limit. -/
theorem inverseLimitEquiv_right_inv (a : XInfinity) :
    ofFamily (toFamily a) = a :=
  ofFamily_toFamily a

/-- The prefix word at resolution 0 is the unique X_0 element. -/
theorem prefixWord_zero (a : XInfinity) :
    prefixWord a 0 = X.empty :=
  Unique.eq_default _

/-- Compatible families are determined by their bit sequences. -/
theorem CompatibleFamily.bit_determines (F : CompatibleFamily) (m : Nat) :
    F.bit m = Omega.last (F.seq (m + 1)).1 :=
  rfl

/-- The No11Inf property is preserved by the inverse limit construction. -/
theorem No11Inf_ofFamily (F : CompatibleFamily) : No11Inf (ofFamily F).1 :=
  (ofFamily F).2

/-- Compatible families form a complete description of infinite stable words. -/
theorem CompatibleFamily_complete :
    Function.Bijective (ofFamily : CompatibleFamily → XInfinity) :=
  inverseLimitEquiv.bijective

-- ══════════════════════════════════════════════════════════════
-- Phase 208: Inverse limit coherence
-- ══════════════════════════════════════════════════════════════

/-- stableValue at resolution m+1 mod F(m+2) equals stableValue at resolution m.
    prop:fold-inverse-limit-xm-xinfty -/
theorem prefixWord_stableValue_coherent (a : XInfinity) (m : Nat) :
    stableValue (prefixWord a (m + 1)) % Nat.fib (m + 2) = stableValue (prefixWord a m) := by
  rw [stableValue_restrict_mod (prefixWord a (m + 1)), restrict_prefixWord]
  exact Nat.mod_eq_of_lt (stableValue_lt_fib (prefixWord a m))

-- ══════════════════════════════════════════════════════════════
-- Phase 210: Prefix surjectivity
-- ══════════════════════════════════════════════════════════════

/-- The prefix projection from XInfinity to X m is surjective.
    prop:fold-inverse-limit-xm-xinfty -/
theorem prefixWord_surjective (m : Nat) :
    Function.Surjective (fun a : XInfinity => prefixWord a m) := by
  intro x
  -- Construct the zero-extension: copy x.1 for indices < m, false otherwise
  let a : Nat → Bool := fun n => if h : n < m then x.1 ⟨n, h⟩ else false
  have hno11 : No11Inf a := by
    intro i ⟨hi, hi1⟩
    simp only [a] at hi hi1
    by_cases h : i < m <;> by_cases h1 : i + 1 < m <;> simp_all
    · exact x.2 i (by simp [Omega.get, h]; exact hi) (by simp [Omega.get, h1]; exact hi1)
  exact ⟨⟨a, hno11⟩, Subtype.ext (funext fun i => by simp [prefixWord, a])⟩

end X

end Omega
