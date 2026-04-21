import Mathlib.Tactic
import Omega.EA.DynamicPrimeRegisterConcatenation

namespace Omega.EA

/-- The fixed base used by the `2^L`-adic affine host. -/
def twoAdicBase (L : ℕ) : ℕ := 2 ^ L

/-- The rank-two affine ambient used for the local `2^L`-adic host model. -/
abbrev TwoAdicAffineAmbient := Fin 2 → ℤ

/-- The additive `B`-adic evaluation of a finite prime-register history. -/
def bAdicValue (B : ℕ) : PrimeRegisterHistory → ℕ
  | [] => 0
  | a :: w => a + B * bAdicValue B w

/-- Canonical digits are strictly positive and strictly smaller than the base. -/
def canonicalDigits (B : ℕ) (w : PrimeRegisterHistory) : Prop :=
  ∀ i : Fin w.length, 0 < w.get i ∧ w.get i < B

/-- The affine action `(r,k) ↦ (x ↦ B^k x + ev_B(r))` on the local rank-two ambient. -/
def twoAdicAffineMap (B : ℕ) (rk : PrimeRegisterHistory × ℕ) :
    TwoAdicAffineAmbient → TwoAdicAffineAmbient :=
  fun x =>
    ![((B ^ rk.2 : ℕ) : ℤ) * x 0 + (bAdicValue B rk.1 : ℤ), ((B ^ rk.2 : ℕ) : ℤ) * x 1]

/-- Canonical finite codes are sent to affine maps via the history/length package. -/
def canonicalAffineCode (L : ℕ) (w : PrimeRegisterHistory) :
    TwoAdicAffineAmbient → TwoAdicAffineAmbient :=
  twoAdicAffineMap (twoAdicBase L) (historyOfWord w)

/-- The finite `n`-prefix of an infinite event stream. -/
def streamPrefix (e : ℕ → ℕ) (n : ℕ) : PrimeRegisterHistory :=
  List.ofFn fun i : Fin n => e i

/-- The compatible family of `B`-adic prefixes of an infinite stream. -/
def streamPoint (B : ℕ) (e : ℕ → ℕ) : ℕ → ℕ :=
  fun n => bAdicValue B (streamPrefix e n)

/-- The affine action intertwines the semidirect multiplication on finite histories. -/
def affineActionHom (L : ℕ) : Prop :=
  ∀ a b x,
    twoAdicAffineMap (twoAdicBase L) (semidirectMul a b) x =
      twoAdicAffineMap (twoAdicBase L) a (twoAdicAffineMap (twoAdicBase L) b x)

/-- The canonical finite `B`-adic codes are faithfully represented by the affine host. -/
def faithfulOnCanonicalCodes (L : ℕ) : Prop :=
  ∀ ⦃u v : PrimeRegisterHistory⦄,
    canonicalDigits (twoAdicBase L) u →
      canonicalDigits (twoAdicBase L) v →
      canonicalAffineCode L u = canonicalAffineCode L v →
      u = v

/-- Equality of all `B`-adic prefixes forces equality of the whole infinite event stream. -/
def infiniteStreamInjective (L : ℕ) : Prop :=
  ∀ ⦃e f : ℕ → ℕ⦄,
    (∀ n, 0 < e n ∧ e n < twoAdicBase L) →
      (∀ n, 0 < f n ∧ f n < twoAdicBase L) →
      streamPoint (twoAdicBase L) e = streamPoint (twoAdicBase L) f →
      e = f

private theorem twoAdicBase_gt_one {L : ℕ} (hL : 0 < L) : 1 < twoAdicBase L := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL) with ⟨n, rfl⟩
  have hpow : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by decide) _)
  simp [twoAdicBase, pow_succ]
  omega

private theorem bAdicValue_historyAdd (B : ℕ) (u v : PrimeRegisterHistory) :
    bAdicValue B (historyAdd u v) = bAdicValue B u + bAdicValue B v := by
  induction u generalizing v with
  | nil =>
      simp [historyAdd, bAdicValue]
  | cons a u ihu =>
      cases v with
      | nil =>
          simp [historyAdd, bAdicValue]
      | cons b v =>
          simp [historyAdd, bAdicValue, ihu, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

private theorem bAdicValue_shiftAction (B k : ℕ) (w : PrimeRegisterHistory) :
    bAdicValue B (shiftAction k w) = B ^ k * bAdicValue B w := by
  induction k with
  | zero =>
      simp [shiftAction]
  | succ k ih =>
      rw [shiftAction] at ih
      rw [shiftAction, List.replicate_succ, List.cons_append, bAdicValue, ih, pow_succ]
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem canonicalDigits_head {B a : ℕ} {w : PrimeRegisterHistory}
    (h : canonicalDigits B (a :: w)) : 0 < a ∧ a < B := by
  simpa [canonicalDigits] using h ⟨0, by simp⟩

private theorem canonicalDigits_tail {B a : ℕ} {w : PrimeRegisterHistory}
    (h : canonicalDigits B (a :: w)) : canonicalDigits B w := by
  intro i
  simpa [canonicalDigits] using h ⟨i.1 + 1, by simpa using Nat.succ_lt_succ i.2⟩

private theorem bAdicValue_injective_of_canonical {B : ℕ} (hB : 1 < B) :
    ∀ ⦃u v : PrimeRegisterHistory⦄,
      canonicalDigits B u →
        canonicalDigits B v →
        bAdicValue B u = bAdicValue B v →
        u = v
  | [], [], _, _, _ => rfl
  | [], b :: v, _, hv, hEq => by
      have hb := canonicalDigits_head hv
      have hpos : 0 < bAdicValue B (b :: v) := by
        simp [bAdicValue, hb.1]
      have hzero : bAdicValue B (b :: v) = 0 := by
        simpa [bAdicValue] using hEq.symm
      exact (Nat.ne_of_gt hpos hzero).elim
  | a :: u, [], hu, _, hEq => by
      have ha := canonicalDigits_head hu
      have hpos : 0 < bAdicValue B (a :: u) := by
        simp [bAdicValue, ha.1]
      have hzero : bAdicValue B (a :: u) = 0 := by
        simpa [bAdicValue] using hEq
      exact (Nat.ne_of_gt hpos hzero).elim
  | a :: u, b :: v, hu, hv, hEq => by
      have ha := canonicalDigits_head hu
      have hb := canonicalDigits_head hv
      have hmodA : bAdicValue B (a :: u) % B = a := by
        simp [bAdicValue, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt ha.2]
      have hmodB : bAdicValue B (b :: v) % B = b := by
        simp [bAdicValue, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb.2]
      have hab : a = b := by
        calc
          a = bAdicValue B (a :: u) % B := by simpa [hmodA]
          _ = bAdicValue B (b :: v) % B := by rw [hEq]
          _ = b := hmodB
      have hmul : B * bAdicValue B u = B * bAdicValue B v := by
        rw [bAdicValue, bAdicValue, hab] at hEq
        exact Nat.add_left_cancel hEq
      have htailVal : bAdicValue B u = bAdicValue B v := by
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hB) hmul
      have htail : u = v :=
        bAdicValue_injective_of_canonical hB (canonicalDigits_tail hu) (canonicalDigits_tail hv)
          htailVal
      simp [hab, htail]

private theorem canonicalDigits_streamPrefix {B : ℕ} {e : ℕ → ℕ}
    (h : ∀ n, 0 < e n ∧ e n < B) (n : ℕ) : canonicalDigits B (streamPrefix e n) := by
  intro i
  simpa [canonicalDigits, streamPrefix, List.get_ofFn] using h i

/-- The `2^L`-adic affine host turns semidirect concatenation into affine composition, is faithful
on finite canonical codes, and separates infinite streams by their compatible `B`-adic prefixes.
    thm:emergent-arithmetic-dynamic-prime-register-2adic-affine-host -/
theorem paper_emergent_arithmetic_dynamic_prime_register_2adic_affine_host
    (L : ℕ) (hL : 0 < L) :
    affineActionHom L ∧ faithfulOnCanonicalCodes L ∧ infiniteStreamInjective L := by
  let B := twoAdicBase L
  have hB : 1 < B := by simpa [B] using twoAdicBase_gt_one hL
  refine ⟨?_, ?_, ?_⟩
  · intro a b x
    ext i <;> fin_cases i
    · simp [twoAdicAffineMap, semidirectMul, bAdicValue_historyAdd, bAdicValue_shiftAction, B,
        pow_add, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    · simp [twoAdicAffineMap, semidirectMul, B, pow_add, mul_assoc, mul_left_comm, mul_comm]
  · intro u v hu hv hAffine
    have hZero :
        ((bAdicValue B u : ℤ) : ℤ) = (bAdicValue B v : ℤ) := by
      simpa [canonicalAffineCode, twoAdicAffineMap, historyOfWord, B] using
        congrArg (fun f => f (fun _ => 0) 0) hAffine
    exact bAdicValue_injective_of_canonical hB hu hv (Int.ofNat.inj hZero)
  · intro e f he hf hPoint
    funext n
    have hPrefixVal :
        bAdicValue B (streamPrefix e (n + 1)) = bAdicValue B (streamPrefix f (n + 1)) := by
      simpa [streamPoint, B] using congrFun hPoint (n + 1)
    have hPrefixEq :
        streamPrefix e (n + 1) = streamPrefix f (n + 1) :=
      bAdicValue_injective_of_canonical hB
        (canonicalDigits_streamPrefix (B := B) he (n + 1))
        (canonicalDigits_streamPrefix (B := B) hf (n + 1))
        hPrefixVal
    have hNth :
        (streamPrefix e (n + 1)).get ⟨n, by simp [streamPrefix]⟩ =
          (streamPrefix f (n + 1)).get ⟨n, by simp [streamPrefix]⟩ := by
      simpa [hPrefixEq]
    have hGetE :
        (streamPrefix e (n + 1)).get ⟨n, by simpa [streamPrefix] using Nat.lt_succ_self n⟩ = e n := by
      simpa [streamPrefix] using
        (List.get_ofFn (f := fun i : Fin (n + 1) => e i) ⟨n, by simp⟩)
    have hGetF :
        (streamPrefix f (n + 1)).get ⟨n, by simpa [streamPrefix] using Nat.lt_succ_self n⟩ = f n := by
      simpa [streamPrefix] using
        (List.get_ofFn (f := fun i : Fin (n + 1) => f i) ⟨n, by simp⟩)
    rw [hGetE, hGetF] at hNth
    exact hNth

end Omega.EA
