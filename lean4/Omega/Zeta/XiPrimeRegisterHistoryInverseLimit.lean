import Mathlib.Data.Nat.Pairing

namespace Omega.Zeta

/-- A `k`-step finite register prefix consists of the base state together with `k` branch labels. -/
abbrev XiPrimeRegisterLayer (X : Type*) (k : ℕ) := X × (Fin k → ℕ)

/-- Truncation keeps the base state and the first `lo` branch labels. -/
def xiPrimeRegisterTruncate {X : Type*} {lo hi : ℕ} (h : lo ≤ hi) :
    XiPrimeRegisterLayer X hi → XiPrimeRegisterLayer X lo
  | (x, a) => (x, fun i => a ⟨i.1, lt_of_lt_of_le i.2 h⟩)

/-- Recursive Gödel-style code for a finite register prefix. -/
def xiPrimeRegisterEncodeDigits : ∀ k : ℕ, (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, a =>
      Nat.pair (a ⟨0, Nat.succ_pos k⟩)
        (xiPrimeRegisterEncodeDigits k (fun i => a ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

/-- The finite register layer embeds into `X × ℕ` via recursive pairing. -/
def xiPrimeRegisterEncode {X : Type*} (k : ℕ) : XiPrimeRegisterLayer X k → X × ℕ
  | (x, a) => (x, xiPrimeRegisterEncodeDigits k a)

theorem xiPrimeRegisterEncodeDigits_injective :
    ∀ k : ℕ, Function.Injective (xiPrimeRegisterEncodeDigits k)
  | 0 => by
      intro a b _
      funext i
      exact Fin.elim0 i
  | k + 1 => by
      intro a b hab
      have hpair :
          Nat.unpair (xiPrimeRegisterEncodeDigits (k + 1) a) =
            Nat.unpair (xiPrimeRegisterEncodeDigits (k + 1) b) := by
        rw [hab]
      have h0 : a ⟨0, Nat.succ_pos k⟩ = b ⟨0, Nat.succ_pos k⟩ := by
        simpa [xiPrimeRegisterEncodeDigits, Nat.unpair_pair] using congrArg Prod.fst hpair
      have htail :
          xiPrimeRegisterEncodeDigits k (fun i => a ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
            xiPrimeRegisterEncodeDigits k (fun i => b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        simpa [xiPrimeRegisterEncodeDigits, Nat.unpair_pair] using congrArg Prod.snd hpair
      have hind := xiPrimeRegisterEncodeDigits_injective k htail
      funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | zero =>
          simpa using h0
      | succ i =>
          have hi' : i < k := Nat.lt_of_succ_lt_succ hi
          exact congrFun hind ⟨i, hi'⟩

theorem xiPrimeRegisterEncode_injective {X : Type*} (k : ℕ) :
    Function.Injective (xiPrimeRegisterEncode (X := X) k) := by
  intro a b hab
  rcases a with ⟨x, aa⟩
  rcases b with ⟨y, bb⟩
  have hx : x = y := congrArg Prod.fst hab
  have hcode : xiPrimeRegisterEncodeDigits k aa = xiPrimeRegisterEncodeDigits k bb :=
    congrArg Prod.snd hab
  cases hx
  exact Prod.ext rfl (xiPrimeRegisterEncodeDigits_injective k hcode)

/-- The inverse-limit object recovered from all truncation-compatible finite register layers. -/
abbrev XiPrimeRegisterStream (X : Type*) := X × (ℕ → ℕ)

/-- A compatible inverse-limit family of finite prime-register layers. -/
abbrev XiPrimeRegisterCompatibleFamily (X : Type*) :=
  { seq : ∀ k : ℕ, XiPrimeRegisterLayer X k //
      ∀ {hi lo : ℕ}, (h : lo ≤ hi) → xiPrimeRegisterTruncate h (seq hi) = seq lo }

/-- Build the compatible family of all finite truncations of an infinite register stream. -/
def xiPrimeRegisterOfStream {X : Type*} (s : XiPrimeRegisterStream X) :
    XiPrimeRegisterCompatibleFamily X :=
  ⟨fun k => (s.1, fun i => s.2 i.1), by
    intro hi lo h
    apply Prod.ext
    · rfl
    · funext i
      rfl⟩

/-- Recover the full register stream from a compatible family by reading the last coordinate of
each finite prefix. -/
def xiPrimeRegisterToStream {X : Type*} (F : XiPrimeRegisterCompatibleFamily X) :
    XiPrimeRegisterStream X :=
  ((F.1 0).1, fun n => (F.1 (n + 1)).2 ⟨n, Nat.lt_succ_self n⟩)

@[simp] theorem xiPrimeRegisterToStream_ofStream {X : Type*} (s : XiPrimeRegisterStream X) :
    xiPrimeRegisterToStream (xiPrimeRegisterOfStream s) = s := by
  rcases s with ⟨x, a⟩
  apply Prod.ext
  · rfl
  · funext n
    rfl

@[simp] theorem xiPrimeRegisterOfStream_toStream {X : Type*}
    (F : XiPrimeRegisterCompatibleFamily X) :
    xiPrimeRegisterOfStream (xiPrimeRegisterToStream F) = F := by
  apply Subtype.ext
  funext k
  apply Prod.ext
  · have h0 := congrArg Prod.fst (F.2 (Nat.zero_le k))
    simpa [xiPrimeRegisterTruncate] using h0.symm
  · funext i
    have hi : i.1 + 1 ≤ k := Nat.succ_le_of_lt i.2
    have hcomp := congrArg Prod.snd (F.2 hi)
    have hcoord := congrArg (fun f => f ⟨i.1, Nat.lt_succ_self i.1⟩) hcomp
    simpa [xiPrimeRegisterOfStream, xiPrimeRegisterToStream, xiPrimeRegisterTruncate] using
      hcoord.symm

/-- The compatible finite-history register tower is equivalent to the infinite branch stream. -/
def xiPrimeRegisterInverseLimitEquiv (X : Type*) :
    XiPrimeRegisterCompatibleFamily X ≃ XiPrimeRegisterStream X where
  toFun := xiPrimeRegisterToStream
  invFun := xiPrimeRegisterOfStream
  left_inv := xiPrimeRegisterOfStream_toStream
  right_inv := xiPrimeRegisterToStream_ofStream

/-- Finite-history register prefixes admit injective recursive encodings, and the compatible tower
of such encodings realizes the inverse-limit register object.
    thm:xi-prime-register-history-inverse-limit -/
theorem paper_xi_prime_register_history_inverse_limit (X : Type*) :
    (∀ k : ℕ, Function.Injective (xiPrimeRegisterEncode (X := X) k)) ∧
      Nonempty (XiPrimeRegisterCompatibleFamily X ≃ XiPrimeRegisterStream X) := by
  exact ⟨fun k => xiPrimeRegisterEncode_injective (X := X) k,
    ⟨xiPrimeRegisterInverseLimitEquiv X⟩⟩

end Omega.Zeta
