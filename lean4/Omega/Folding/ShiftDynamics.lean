import Omega.Folding.InverseLimitTopology
import Omega.Graph.TransferMatrix

namespace Omega.X

/-- The left shift on XInfinity: σ(a)(i) = a(i+1).
    cor:pom-shift-conjugacy-on-godel-image -/
def shift (a : XInfinity) : XInfinity :=
  ⟨fun i => a.1 (i + 1), fun i h => a.2 (i + 1) h⟩

/-- The shift map is continuous (composition of continuous projections).
    prop:shift-continuous -/
theorem continuous_shift : Continuous shift := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply (i + 1)).comp continuous_subtype_val

/-- The shift map is surjective: prepend false to any sequence.
    prop:shift-surjective -/
theorem shift_surjective : Function.Surjective shift := by
  intro b
  refine ⟨⟨fun i => if i = 0 then false else b.1 (i - 1), fun i ⟨hi, hi1⟩ => ?_⟩, ?_⟩
  · -- No11Inf proof for prepended sequence
    cases i with
    | zero => simp at hi
    | succ i =>
      simp only [Nat.succ_ne_zero, ↓reduceIte] at hi hi1
      exact b.2 i ⟨hi, by rwa [show i + 1 + 1 - 1 = i + 1 from by omega] at hi1⟩
  · -- shift of constructed sequence = b
    ext i; simp [shift]

/-- Coordinate formula for the left shift: the i-th entry of σ(a) equals a(i+1).
    lem:shift-val -/
theorem shift_val (a : XInfinity) (i : Nat) : (shift a).1 i = a.1 (i + 1) := rfl

/-- The n-fold iterate of the left shift. -/
def shiftN : Nat → XInfinity → XInfinity
  | 0, a => a
  | n + 1, a => shift (shiftN n a)

/-- Coordinate formula for the n-fold shift: σⁿ(a)(i) = a(i+n). -/
theorem shiftN_val : ∀ (n : Nat) (a : XInfinity) (i : Nat),
    (shiftN n a).1 i = a.1 (i + n)
  | 0, a, i => by simp [shiftN]
  | n + 1, a, i => by simp [shiftN, shift_val, shiftN_val n a (i + 1)]; ring_nf

/-- The n-fold shift is continuous. -/
theorem continuous_shiftN : ∀ (n : Nat), Continuous (shiftN n)
  | 0 => continuous_id
  | n + 1 => continuous_shift.comp (continuous_shiftN n)

/-- The all-false infinite sequence (the unique fixed point of shift).
    def:shift-allFalse -/
def allFalse : XInfinity := ⟨fun _ => false, fun _ h => by exact absurd h.1 Bool.false_ne_true⟩

/-- prop:shift-allFalse-fixed -/
@[simp] theorem shift_allFalse : shift allFalse = allFalse :=
  Subtype.ext (funext fun _ => rfl)

/-- shift(a) = a iff a is the all-false sequence.
    thm:shift-fixed-iff -/
theorem shift_fixed_iff (a : XInfinity) : shift a = a ↔ a = allFalse := by
  constructor
  · intro h
    apply Subtype.ext; funext i
    have hEq : ∀ j, a.1 (j + 1) = a.1 j := fun j => congr_fun (congr_arg Subtype.val h) j
    have hConst : ∀ i, a.1 i = a.1 0 := by
      intro i; induction i with
      | zero => rfl
      | succ n ih => exact (hEq n).trans ih
    cases h0 : a.1 0 with
    | false => exact (hConst i).trans h0
    | true => exact absurd ⟨(hConst 0).symm ▸ h0, (hConst 1).symm ▸ h0⟩ (a.2 0)
  · intro h; rw [h, shift_allFalse]

/-- The shift is not injective (both allFalse and (true,false,false,...) map to allFalse).
    prop:shift-not-injective -/
theorem shift_not_injective : ¬ Function.Injective shift := by
  intro hInj
  have hNo11 : No11Inf (fun i => if i = 0 then true else false) := by
    intro i ⟨hi, hi1⟩
    by_cases h0 : i = 0
    · subst h0; simp at hi1
    · simp [h0] at hi
  let a : XInfinity := ⟨_, hNo11⟩
  have hShift : shift a = shift allFalse := by
    apply Subtype.ext; funext i
    show (if i + 1 = 0 then true else false) = false
    simp
  have hab := congr_fun (congr_arg Subtype.val (hInj hShift)) 0
  -- hab : a.1 0 = allFalse.1 0, need to show this is true = false
  change (if (0 : Nat) = 0 then true else false) = false at hab
  simp at hab

/-- The period-3 sequence: true at positions 0, 3, 6, ...
    def:period3-seq -/
def period3Seq : XInfinity :=
  ⟨fun i => decide (i % 3 = 0), fun i ⟨hi, hi1⟩ => by simp at hi hi1; omega⟩

/-- The period-3 sequence has period 3 under shift.
    thm:shiftN-three-period3 -/
theorem shiftN_three_period3 : shiftN 3 period3Seq = period3Seq := by
  apply Subtype.ext; funext i; simp [shiftN, shift, period3Seq]; omega

/-- The period-3 sequence is NOT a fixed point of shift.
    thm:shift-period3-ne -/
theorem shift_period3_ne : shift period3Seq ≠ period3Seq := by
  intro h; have := congr_fun (congr_arg Subtype.val h) 0
  simp [shift, period3Seq] at this

/-- The period-2 sequence: true at positions 0, 2, 4, ...
    def:period2-seq -/
def period2Seq : XInfinity :=
  ⟨fun i => decide (i % 2 = 0), fun i ⟨hi, hi1⟩ => by simp at hi hi1; omega⟩

/-- The period-2 sequence has period 2 under shift.
    thm:shiftN-two-period2 -/
theorem shiftN_two_period2 : shiftN 2 period2Seq = period2Seq := by
  apply Subtype.ext; funext i; simp [shiftN, shift, period2Seq]; omega

/-- The period-2 sequence is not a fixed point.
    cor:shift-period2-ne -/
theorem shift_period2_ne : shift period2Seq ≠ period2Seq := by
  intro h; have := congr_fun (congr_arg Subtype.val h) 0
  simp [shift, period2Seq] at this

/-- Period-2 is minimal: not fixed, but period 2.
    cor:shift-period2-minimal -/
theorem period2_minimal :
    shift period2Seq ≠ period2Seq ∧ shiftN 2 period2Seq = period2Seq :=
  ⟨shift_period2_ne, shiftN_two_period2⟩

/-- Period-3 is minimal: not fixed, not period 2, but period 3.
    cor:shift-period3-minimal -/
theorem period3_minimal :
    shift period3Seq ≠ period3Seq ∧ shiftN 2 period3Seq ≠ period3Seq ∧
    shiftN 3 period3Seq = period3Seq := by
  refine ⟨shift_period3_ne, ?_, shiftN_three_period3⟩
  intro h; have := congr_fun (congr_arg Subtype.val h) 0
  simp [shiftN, shift, period3Seq] at this

/-- The period-4 sequence: true at positions 0, 4, 8, ...
    def:shift-period4-seq -/
def period4Seq : XInfinity :=
  ⟨fun i => decide (i % 4 = 0), fun i ⟨hi, hi1⟩ => by simp at hi hi1; omega⟩

/-- The period-4 sequence has period 4 under shift.
    cor:shift-period4-orbit -/
theorem shiftN_four_period4 : shiftN 4 period4Seq = period4Seq := by
  apply Subtype.ext; funext i; simp [shiftN, shift, period4Seq]; omega

end Omega.X

namespace Omega

/-! ### Discrete entropy skeleton (cor:folding-stable-syntax-entropy-logqdim, Stage 1)

The finite stable syntax spaces X_m satisfy:
- Fibonacci recurrence: |X_{m+2}| = |X_{m+1}| + |X_m|
- Growth bounds: |X_m| ≤ |X_{m+1}| ≤ 2 · |X_m|
- Transfer matrix representation: |X_m| = (A^m)_{00} + (A^m)_{01}
-/

/-- |X_{m+2}| = |X_{m+1}| + |X_m| (Fibonacci recurrence for stable word counts).
    cor:folding-stable-syntax-entropy-logqdim-card-recurrence -/
theorem card_X_recurrence (m : Nat) :
    Fintype.card (X (m + 2)) = Fintype.card (X (m + 1)) + Fintype.card (X m) := by
  simp only [X.card_eq_fib]
  exact fib_succ_succ' (m + 2)

/-- |X_m| ≤ |X_{m+1}| ≤ 2 · |X_m| (Fibonacci ratio bounds).
    cor:folding-stable-syntax-entropy-logqdim-ratio-bounds -/
theorem card_X_ratio_bounds (m : Nat) :
    Fintype.card (X m) ≤ Fintype.card (X (m + 1)) ∧
    Fintype.card (X (m + 1)) ≤ 2 * Fintype.card (X m) := by
  simp only [X.card_eq_fib]
  constructor
  · exact Nat.fib_mono (by omega)
  · -- Nat.fib (m+3) ≤ 2 * Nat.fib (m+2)
    calc Nat.fib (m + 3)
        = Nat.fib (m + 2) + Nat.fib (m + 1) := fib_succ_succ' (m + 1)
      _ ≤ Nat.fib (m + 2) + Nat.fib (m + 2) :=
          Nat.add_le_add_left (Nat.fib_mono (by omega)) _
      _ = 2 * Nat.fib (m + 2) := by omega

/-- |X_m| = (A^m)_{00} + (A^m)_{01} where A is the golden-mean adjacency matrix.
    cor:folding-stable-syntax-entropy-logqdim-matrix-sum -/
theorem card_X_eq_matrix_sum (m : Nat) :
    (Fintype.card (X m) : ℤ) =
      (Graph.goldenMeanAdjacency ^ m) 0 0 + (Graph.goldenMeanAdjacency ^ m) 0 1 := by
  rw [X.card_eq_fib]
  exact (Graph.goldenMeanAdjacency_row_sum m).symm

/-! ### Lucas numbers -/

/-- The Lucas sequence: L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n.
    def:lucas-number -/
def lucasNum : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => lucasNum (n + 1) + lucasNum n

@[simp] theorem lucasNum_zero : lucasNum 0 = 2 := rfl
@[simp] theorem lucasNum_one : lucasNum 1 = 1 := rfl
theorem lucasNum_two : lucasNum 2 = 3 := rfl
theorem lucasNum_three : lucasNum 3 = 4 := rfl
theorem lucasNum_nine : lucasNum 9 = 76 := by native_decide
@[simp] theorem lucasNum_succ_succ (n : Nat) :
    lucasNum (n + 2) = lucasNum (n + 1) + lucasNum n := rfl

/-- L_n = F_{n+1} + F_{n-1} for n ≥ 1. -/
private theorem lucasNum_eq_fib_aux :
    ∀ m : Nat, lucasNum (m + 1) = Nat.fib (m + 2) + Nat.fib m
  | 0 => by native_decide
  | 1 => by native_decide
  | m + 2 => by
    rw [lucasNum_succ_succ, lucasNum_eq_fib_aux (m + 1), lucasNum_eq_fib_aux m]
    -- Use native_decide for m=0,1 then the recurrence handles the rest uniformly
    -- Actually the omega issue is Nat.fib normalization. Just native_decide small + fallback.
    simp only [ fib_succ_succ']
    omega

/-- L_n = F_{n+1} + F_{n-1} for n ≥ 1.
    prop:lucas-fibonacci-identity -/
theorem lucasNum_eq_fib (n : Nat) (hn : 1 ≤ n) :
    lucasNum n = Nat.fib (n + 1) + Nat.fib (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [show m + 1 - 1 = m from by omega]
  exact lucasNum_eq_fib_aux m

/-- trace(A^n) = F_{n+1} + F_{n-1} for n ≥ 1 (= Lucas number).
    thm:transfer-matrix-pow-trace -/
theorem goldenMeanAdjacency_pow_trace (n : Nat) (hn : 1 ≤ n) :
    (Graph.goldenMeanAdjacency ^ n).trace =
      (Nat.fib (n + 1) : ℤ) + Nat.fib (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Matrix.trace, Matrix.diag, show m + 1 - 1 = m from by omega]
  rw [Fin.sum_univ_two]
  rw [Graph.goldenMeanAdjacency_pow_00, Graph.goldenMeanAdjacency_pow_11]

-- ══════════════════════════════════════════════════════════════
-- Lucas number identities
-- ══════════════════════════════════════════════════════════════

/-- Lucas numbers are positive.
    bridge:lucas-num-pos -/
theorem lucasNum_pos : ∀ n : Nat, 0 < lucasNum n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by rw [lucasNum_succ_succ]; exact Nat.add_pos_left (lucasNum_pos (n + 1)) _

/-- L(n) * F(n) = F(2n) for n ≥ 1.
    bridge:lucas-fibonacci-product -/
theorem lucasNum_mul_fib (n : Nat) (hn : 1 ≤ n) :
    lucasNum n * Nat.fib n = Nat.fib (2 * n) := by
  -- Cast to ℤ where subtraction works, use fib_double identity
  suffices h : (lucasNum n * Nat.fib n : ℤ) = (Nat.fib (2 * n) : ℤ) from Nat.cast_injective h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasNum_eq_fib (m + 1) (by omega)]
  simp only [show m + 1 - 1 = m from by omega, show m + 1 + 1 = m + 2 from by omega]
  push_cast
  -- (F(m+2) + F(m)) * F(m+1) = F(2*(m+1))
  -- F(2*(m+1)) = F(m+1) * (2*F(m+2) - F(m+1)) in ℤ
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring]
  rw [show (Nat.fib (2 * m + 2) : ℤ) = Nat.fib (m + 1) * (2 * Nat.fib (m + 2) - Nat.fib (m + 1)) from by
    have := Nat.fib_two_mul (m + 1)
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring] at this
    have hge : Nat.fib (m + 1) ≤ 2 * Nat.fib (m + 2) := by
      calc Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
        _ ≤ 2 * Nat.fib (m + 2) := Nat.le_mul_of_pos_left _ (by omega)
    zify [hge] at this ⊢; linarith]
  -- Now: (↑F(m+2) + ↑F(m)) * ↑F(m+1) = ↑F(m+1) * (2*↑F(m+2) - ↑F(m+1))
  have hrec : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast Nat.fib_add_two
  nlinarith

/-- F(2k) = F(k) · L(k): Fibonacci doubling via Lucas numbers.
    prop:fib-double-lucas -/
theorem fib_double_eq_mul_lucas (k : Nat) :
    Nat.fib (2 * k) = Nat.fib k * lucasNum k := by
  cases k with
  | zero => simp
  | succ n =>
    have := lucasNum_mul_fib (n + 1) (by omega)
    linarith [Nat.mul_comm (Nat.fib (n + 1)) (lucasNum (n + 1))]

/-- Lucas Cassini: L(n)² - L(n-1)·L(n+1) = 5·(-1)^n for n ≥ 1.
    bridge:lucas-cassini -/
theorem lucasNum_cassini (n : Nat) (hn : 1 ≤ n) :
    (lucasNum n : ℤ) ^ 2 - (lucasNum (n - 1) : ℤ) * (lucasNum (n + 1) : ℤ) =
    5 * (-1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [show m + 1 - 1 = m from by omega]
  induction m with
  | zero => native_decide
  | succ k ih =>
    -- L(k+2)² - L(k+1)*L(k+3) = 5*(-1)^(k+2)
    rw [show k + 1 + 1 = k + 2 from by omega, show k + 1 + 1 + 1 = k + 3 from by omega]
    rw [show (lucasNum (k + 3) : ℤ) = lucasNum (k + 2) + lucasNum (k + 1) from by
      exact_mod_cast lucasNum_succ_succ (k + 1)]
    rw [show k + 1 + 1 = k + 2 from by omega] at ih
    have ih' := ih (by omega)
    have hpow : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
    have hrec : (lucasNum (k + 2) : ℤ) = lucasNum (k + 1) + lucasNum k := by
      exact_mod_cast lucasNum_succ_succ k
    rw [hpow]; nlinarith

/-- Lucas doubling: L(2n) = L(n)² - 2·(-1)^n for n ≥ 1.
    bridge:lucas-double -/
theorem lucasNum_double (n : Nat) (hn : 1 ≤ n) :
    (lucasNum (2 * n) : ℤ) = (lucasNum n : ℤ) ^ 2 - 2 * (-1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasNum_eq_fib (2 * (m + 1)) (by omega)]
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 from by omega]
  rw [lucasNum_eq_fib (m + 1) (by omega)]
  simp only [show m + 1 + 1 = m + 2 from by omega, show m + 1 - 1 = m from by omega]
  rw [fib_double_plus_one (m + 1), fib_double_plus_one m]
  -- Need Cassini: F(m+2)·F(m) - F(m+1)² = (-1)^(m+1)
  suffices cassini : (Nat.fib (m + 2) : ℤ) * Nat.fib m - (Nat.fib (m + 1) : ℤ) ^ 2 = (-1) ^ (m + 1) by
    push_cast; nlinarith
  induction m with
  | zero => native_decide
  | succ k ih =>
    have hrec1 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
      have := @Nat.fib_add_two (k + 1); linarith
    have hrec2 : (Nat.fib (k + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib k := by
      have := @Nat.fib_add_two k; linarith
    have hpow : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
    have ih' := ih (by omega)
    rw [show k + 1 + 1 = k + 2 from by omega] at *
    rw [hrec1, hpow]; nlinarith

/-- Lucas doubling unconditional: L(2n) = L(n)² - 2·(-1)^n for all n.
    prop:lucas-double-unconditional -/
theorem lucasNum_double_uncond (n : Nat) :
    (lucasNum (2 * n) : ℤ) = (lucasNum n : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ n := by
  cases n with
  | zero => simp [lucasNum]
  | succ m => exact lucasNum_double (m + 1) (by omega)

/-- L(n)² = 5·F(n)² + 4·(-1)^n for n ≥ 1.
    bridge:lucas-fibonacci-square -/
theorem lucasNum_sq (n : Nat) (hn : 1 ≤ n) :
    (lucasNum n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasNum_eq_fib (m + 1) (by omega)]
  simp only [show m + 1 + 1 = m + 2 from by omega, show m + 1 - 1 = m from by omega]
  -- L = F(m+2) + F(m), need (F(m+2)+F(m))² = 5F(m+1)² + 4(-1)^(m+1)
  -- Expand LHS = F(m+2)² + 2F(m+2)F(m) + F(m)²
  -- Use Cassini: F(m+2)F(m) = F(m+1)² + (-1)^(m+1)
  -- So LHS = F(m+2)² + 2(F(m+1)² + (-1)^(m+1)) + F(m)²
  --        = F(m+2)² + F(m)² + 2F(m+1)² + 2(-1)^(m+1)
  -- Also F(m+2) = F(m+1)+F(m), so F(m+2)² = F(m+1)² + 2F(m+1)F(m) + F(m)²
  -- LHS = F(m+1)² + 2F(m+1)F(m) + F(m)² + F(m)² + 2F(m+1)² + 2(-1)^(m+1)
  --      = 3F(m+1)² + 2F(m+1)F(m) + 2F(m)² + 2(-1)^(m+1)
  -- RHS = 5F(m+1)² + 4(-1)^(m+1)
  -- Need: 3F(m+1)² + 2F(m+1)F(m) + 2F(m)² + 2(-1)^(m+1) = 5F(m+1)² + 4(-1)^(m+1)
  -- i.e., 2F(m+1)F(m) + 2F(m)² = 2F(m+1)² + 2(-1)^(m+1)
  -- i.e., F(m)(F(m+1)+F(m)) = F(m+1)² + (-1)^(m+1) = F(m+2)F(m) [Cassini]
  -- i.e., F(m)F(m+2) = F(m+2)F(m). ✓ Always true!
  -- Let me just use nlinarith with Cassini and fib recurrence.
  have cassini : (Nat.fib (m + 2) : ℤ) * Nat.fib m - (Nat.fib (m + 1) : ℤ) ^ 2 = (-1) ^ (m + 1) := by
    -- Reuse the inline Cassini from lucasNum_double
    induction m with
    | zero => native_decide
    | succ k ih =>
      have hr1 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
        have := @Nat.fib_add_two (k + 1); linarith
      have hr2 : (Nat.fib (k + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib k := by
        have := @Nat.fib_add_two k; linarith
      have hp : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
      have ih' := ih (by omega)
      rw [show k + 1 + 1 = k + 2 from by omega] at *
      rw [hr1, hp]; nlinarith
  have hrec : (Nat.fib (m + 2) : ℤ) = Nat.fib (m + 1) + Nat.fib m := by
    have := @Nat.fib_add_two m; linarith
  push_cast; nlinarith

/-- L(n)² = 5·F(n)² + 4·(-1)^n, unconditional (handles n=0 separately).
    prop:lucas-fibonacci-square-unconditional -/
theorem lucas_sq_eq_five_fib_sq (n : Nat) :
    (lucasNum n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1 : ℤ) ^ n := by
  cases n with
  | zero => simp [lucasNum]
  | succ m => exact lucasNum_sq (m + 1) (by omega)

/-- L(n) + F(n) = 2·F(n+1) for n ≥ 1.
    bridge:lucas-add-fib -/
theorem lucasNum_add_fib (n : Nat) (hn : 1 ≤ n) :
    lucasNum n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasNum_eq_fib (m + 1) (by omega)]
  simp only [show m + 1 + 1 = m + 2 from by omega, show m + 1 - 1 = m from by omega]
  -- (F(m+2) + F(m)) + F(m+1) = 2·F(m+2)
  -- F(m+2) = F(m+1) + F(m), so F(m+2) + F(m) + F(m+1) = F(m+1) + F(m) + F(m) + F(m+1) = 2F(m+1) + 2F(m)... no
  -- F(m+2) + F(m) + F(m+1) = F(m+2) + (F(m) + F(m+1)) = F(m+2) + F(m+2) = 2F(m+2) ✓
  have hrec : Nat.fib m + Nat.fib (m + 1) = Nat.fib (m + 2) := by
    have := Nat.fib_add_two (n := m); omega
  omega

/-- L(n) - F(n) = 2·F(n-1) for n ≥ 1.
    bridge:lucas-sub-fib -/
theorem lucasNum_sub_fib (n : Nat) (hn : 1 ≤ n) :
    lucasNum n - Nat.fib n = 2 * Nat.fib (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lucasNum_eq_fib (m + 1) (by omega)]
  simp only [show m + 1 + 1 = m + 2 from by omega, show m + 1 - 1 = m from by omega]
  -- (F(m+2) + F(m)) - F(m+1) = 2·F(m)
  -- F(m+2) = F(m+1) + F(m), so (F(m+1)+F(m)+F(m)) - F(m+1) = 2F(m)
  have hrec : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  omega


/-- Lucas number parity: L(n) is even iff 3 ∣ n.
    bridge:lucas-parity -/
theorem lucasNum_even_iff (n : Nat) : 2 ∣ lucasNum n ↔ 3 ∣ n := by
  -- L(n) mod 2 has period 3: L(0)=2(even), L(1)=1(odd), L(2)=3(odd), L(3)=4(even), ...
  -- Pattern: even, odd, odd, even, odd, odd, ...
  -- 2|L(n) ↔ n ≡ 0 (mod 3)
  -- L(n) mod 2 has period 3: even, odd, odd, even, ...
  -- Key lemma: L(n+3) = 2L(n+1) + L(n), so L(n+3) mod 2 = L(n) mod 2
  have hperiod : ∀ k, 2 ∣ lucasNum (k + 3) ↔ 2 ∣ lucasNum k := by
    intro k
    have h1 : lucasNum (k + 3) = lucasNum (k + 2) + lucasNum (k + 1) := lucasNum_succ_succ (k + 1)
    have h2 : lucasNum (k + 2) = lucasNum (k + 1) + lucasNum k := lucasNum_succ_succ k
    constructor <;> intro h <;> omega
  constructor
  · -- Forward: 2|L(n) → 3|n. Strong induction.
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro h
      match n with
      | 0 => exact dvd_zero 3
      | 1 => exfalso; rw [lucasNum_one] at h; omega
      | 2 => exfalso; rw [lucasNum_two] at h; omega
      | n + 3 =>
        have := ih n (by omega) ((hperiod n).mp h)
        exact ⟨n / 3 + 1, by omega⟩
  · -- Backward: 3|n → 2|L(n). Induction on k where n = 3k.
    intro ⟨k, hk⟩; subst hk
    induction k with
    | zero => simp
    | succ j ih =>
      rw [show 3 * (j + 1) = 3 * j + 3 from by ring]
      exact (hperiod (3 * j)).mpr ih

/-- 3 ∣ L(n) iff n ≡ 2 (mod 4).
    bridge:lucas-three-divisibility -/
theorem lucasNum_three_dvd (n : Nat) : 3 ∣ lucasNum n ↔ n % 4 = 2 := by
  -- L(n) mod 3 has period 4: L(0)=2, L(1)=1, L(2)=3, L(3)=4, L(4)=7, ...
  -- mod 3: 2, 1, 0, 1, 1, 2, 0, 2, 2, 1, 0, 1, ... period 8? Actually let me check:
  -- L mod 3: 2,1,0,1,1,2,0,2,2,1,0,1,... period 8. Hmm, 3|L(n) when n%8=2 or n%8=6.
  -- That's n%4=2. ✓
  have hperiod : ∀ k, 3 ∣ lucasNum (k + 4) ↔ 3 ∣ lucasNum k := by
    intro k
    -- L(k+4) = L(k+3)+L(k+2) = (L(k+2)+L(k+1))+(L(k+1)+L(k)) = L(k+2)+2L(k+1)+L(k)
    -- = (L(k+1)+L(k))+2L(k+1)+L(k) = 3L(k+1)+2L(k)
    -- So L(k+4) ≡ 2L(k) mod 3. And gcd(2,3)=1, so 3|L(k+4) ↔ 3|L(k).
    have h1 : lucasNum (k + 4) = lucasNum (k + 3) + lucasNum (k + 2) := lucasNum_succ_succ (k + 2)
    have h2 : lucasNum (k + 3) = lucasNum (k + 2) + lucasNum (k + 1) := lucasNum_succ_succ (k + 1)
    have h3 : lucasNum (k + 2) = lucasNum (k + 1) + lucasNum k := lucasNum_succ_succ k
    -- L(k+4) = 3L(k+1) + 2L(k)
    constructor
    · intro h
      have h2L : 3 ∣ lucasNum k * 2 := by omega
      have hcop : Nat.Coprime 3 2 := by decide
      exact (hcop.dvd_of_dvd_mul_right h2L)
    · intro h; exact ⟨lucasNum (k + 1) + (2 * (lucasNum k / 3)), by omega⟩
  constructor
  · induction n using Nat.strongRecOn with
    | _ n ih =>
      intro h; match n with
      | 0 => exfalso; rw [lucasNum_zero] at h; omega
      | 1 => exfalso; rw [lucasNum_one] at h; omega
      | 2 => rfl
      | 3 => exfalso; rw [lucasNum_three] at h; omega
      | n + 4 => have := ih n (by omega) ((hperiod n).mp h); omega
  · intro h
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 => omega
      | 1 => omega
      | 2 => rw [lucasNum_two]
      | 3 => omega
      | n + 4 =>
        have hmod : (n + 4) % 4 = n % 4 := by omega
        rw [hmod] at h
        exact (hperiod n).mpr (ih n (by omega) h)

/-- Lucas Cassini (Nat, even): L(n)² = L(n-1)·L(n+1) + 5 when n even, n ≥ 2.
    bridge:lucas-cassini-nat -/
theorem lucasNum_cassini_even (n : Nat) (hn : 2 ≤ n) (heven : Even n) :
    lucasNum n ^ 2 = lucasNum (n - 1) * lucasNum (n + 1) + 5 := by
  have hcas := lucasNum_cassini n (by omega)
  have hpow : ((-1 : ℤ) ^ n) = 1 := Even.neg_one_pow heven
  have hpos := lucasNum_pos (n - 1)
  have hpos2 := lucasNum_pos (n + 1)
  zify; linarith

/-- Lucas Cassini (Nat, odd): L(n)² + 5 = L(n-1)·L(n+1) when n odd, n ≥ 1.
    bridge:lucas-cassini-nat -/
theorem lucasNum_cassini_odd (n : Nat) (hn : 1 ≤ n) (hodd : ¬ Even n) :
    lucasNum n ^ 2 + 5 = lucasNum (n - 1) * lucasNum (n + 1) := by
  have hcas := lucasNum_cassini n hn
  have hoddN : Odd n := by rwa [Nat.not_even_iff_odd] at hodd
  have hpow : ((-1 : ℤ) ^ n) = -1 := Odd.neg_one_pow hoddN
  zify; linarith

/-- F(n) ≤ L(n) for n ≥ 1.
    bridge:fib-lucas-bound -/
theorem fib_le_lucasNum (n : Nat) (hn : 1 ≤ n) : Nat.fib n ≤ lucasNum n := by
  have h := lucasNum_add_fib n hn
  -- L + F = 2F(n+1) ≥ 2F ≥ F + F ≥ F, so L ≥ 0 and F ≤ L+F = 2F(n+1)
  -- Actually: L ≥ F ↔ L + F ≥ 2F ↔ 2F(n+1) ≥ 2F(n) ↔ F(n+1) ≥ F(n), which is true.
  have := Nat.fib_mono (show n ≤ n + 1 from by omega)
  omega

/-- L(n) ≤ 2·F(n+1) for n ≥ 1.
    bridge:lucas-upper-bound -/
theorem lucasNum_le_two_fib_succ (n : Nat) (hn : 1 ≤ n) :
    lucasNum n ≤ 2 * Nat.fib (n + 1) := by
  have := lucasNum_add_fib n hn; omega

/-- F(n+1)² - F(n)·F(n+2) = (-1)^n for n ≥ 1.
    bridge:cassini-variant -/
theorem fib_succ_sq_sub_prod (n : Nat) (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) = (-1) ^ n := by
  have hcas := Graph.fib_cassini n hn
  have hfib : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
    have := Nat.fib_add_two (n := n); linarith
  -- F(n+1)² - F(n)*F(n+2) = F(n+1)² - F(n)*(F(n)+F(n+1))
  -- = F(n+1)² - F(n)² - F(n)*F(n+1) = F(n+1)*(F(n+1)-F(n)) - F(n)²
  -- Need F(n-1) = F(n+1) - F(n), i.e., F(n+1) = F(n) + F(n-1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [show m + 1 - 1 = m from by omega, show m + 1 + 1 = m + 2 from by omega,
    show m + 1 + 2 = m + 3 from by omega] at *
  have hfib2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    have := Nat.fib_add_two (n := m); linarith
  nlinarith

/-- F(n)·F(n+2) = F(n+1)² + (-1)^(n+1).
    bridge:fib-adjacent-product -/
theorem fib_adjacent_product (n : Nat) (hn : 1 ≤ n) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) = (Nat.fib (n + 1) : ℤ) ^ 2 + (-1) ^ (n + 1) := by
  have h := fib_succ_sq_sub_prod n hn
  have hpow : ((-1 : ℤ) ^ (n + 1)) = -((-1) ^ n) := by ring
  linarith

/-- Fibonacci rectangle identity: F(n)·F(n+3) = F(n+1)·F(n+2) + (-1)^(n+1).
    bridge:fib-rectangle-identity -/
theorem fib_rectangle (n : Nat) :
    (Nat.fib n : ℤ) * Nat.fib (n + 3) =
    (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 2) + (-1) ^ (n + 1) := by
  -- F(n+3) = F(n+2) + F(n+1), so F(n)*F(n+3) = F(n)*F(n+2) + F(n)*F(n+1)
  -- F(n)*F(n+2) = F(n+1)^2 + (-1)^(n+1) by fib_adjacent_product
  -- F(n)*F(n+1) = F(n+1)*F(n)
  -- So F(n)*F(n+3) = F(n+1)^2 + (-1)^(n+1) + F(n+1)*F(n) = F(n+1)*(F(n+1)+F(n)) + (-1)^(n+1)
  -- = F(n+1)*F(n+2) + (-1)^(n+1) ✓
  -- Special case of Vajda: fib_vajda n 1 2 gives
  -- F(n+1)*F(n+2) - F(n)*F(n+3) = (-1)^n*F(1)*F(2) = (-1)^n
  have hv := fib_vajda n 1 2
  simp only [show Nat.fib 1 = 1 from rfl, show Nat.fib 2 = 1 from rfl,
    show n + 1 + 2 = n + 3 from by omega, Nat.cast_one, mul_one] at hv
  have hpow : (-1 : ℤ) ^ (n + 1) = -((-1) ^ n) := by ring
  linarith [hv, hpow]

-- ══════════════════════════════════════════════════════════════
-- Phase 186
-- ══════════════════════════════════════════════════════════════

/-- Lucas-Fibonacci Wronskian (even): L_n·F_{n+1} = L_{n+1}·F_n + 2 for even n ≥ 2. -/
theorem lucasNum_fib_wronskian_even (n : Nat) (hn : 2 ≤ n) (heven : Even n) :
    lucasNum n * Nat.fib (n + 1) = lucasNum (n + 1) * Nat.fib n + 2 := by
  rw [lucasNum_eq_fib n (by omega), lucasNum_eq_fib (n + 1) (by omega)]
  rw [show n + 1 - 1 = n from by omega, show n + 1 + 1 = n + 2 from by omega]
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h2
  have hcas := fib_cassini_even n heven
  nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n - 1))]

/-- Lucas-Fibonacci Wronskian (odd): L_{n+1}·F_n = L_n·F_{n+1} + 2 for odd n ≥ 1. -/
theorem lucasNum_fib_wronskian_odd (n : Nat) (hn : 1 ≤ n) (hodd : ¬ Even n) :
    lucasNum (n + 1) * Nat.fib n = lucasNum n * Nat.fib (n + 1) + 2 := by
  rw [lucasNum_eq_fib n hn, lucasNum_eq_fib (n + 1) (by omega)]
  rw [show n + 1 - 1 = n from by omega, show n + 1 + 1 = n + 2 from by omega]
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h2
  have hcas := fib_cassini_odd n hodd
  nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n - 1))]

-- ══════════════════════════════════════════════════════════════
-- Phase 202: Lucas-Fibonacci squared identity
-- ══════════════════════════════════════════════════════════════

/-- L(n)^2 = 5*F(n)^2 + 4 for even n >= 1.
    bridge:lucas-fibonacci-identity -/
theorem lucasNum_sq_even (n : Nat) (hn : 1 ≤ n) (heven : Even n) :
    lucasNum n ^ 2 = 5 * Nat.fib n ^ 2 + 4 := by
  rw [lucasNum_eq_fib n hn]
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h2
  have hcas := fib_cassini_even n heven
  nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n - 1)),
             sq_nonneg (Nat.fib (n + 1))]

/-- L(n)^2 + 4 = 5*F(n)^2 for odd n.
    bridge:lucas-fibonacci-identity -/
theorem lucasNum_sq_odd (n : Nat) (hodd : ¬ Even n) :
    lucasNum n ^ 2 + 4 = 5 * Nat.fib n ^ 2 := by
  have hn : 1 ≤ n := by rcases n with _ | n; exact absurd ⟨0, rfl⟩ hodd; omega
  rw [lucasNum_eq_fib n hn]
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h2
  have hcas := fib_cassini_odd n hodd
  nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n - 1)),
             sq_nonneg (Nat.fib (n + 1))]

-- ══════════════════════════════════════════════════════════════
-- Phase 205: Trace = Lucas number (lucasNum form)
-- ══════════════════════════════════════════════════════════════

/-- tr(N_tau^m) = L(m), trace of golden mean adjacency power = Lucas number.
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem goldenMeanAdjacency_pow_trace_lucas (m : Nat) (hm : 1 ≤ m) :
    (Graph.goldenMeanAdjacency ^ m).trace = (lucasNum m : ℤ) := by
  rw [goldenMeanAdjacency_pow_trace m hm, lucasNum_eq_fib m hm]; push_cast; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 206: Lucas addition formula + partial sum
-- ══════════════════════════════════════════════════════════════

/-- Lucas-Fibonacci addition formula: L(m+n+2) = L(m+1)*F(n+2) + L(m)*F(n+1).
    bridge:lucas-fib-addition-formula -/
theorem lucasNum_add_formula : ∀ (m n : Nat),
    (lucasNum (m + n + 2) : ℤ) =
    (lucasNum (m + 1) : ℤ) * (Nat.fib (n + 2) : ℤ) +
    (lucasNum m : ℤ) * (Nat.fib (n + 1) : ℤ)
  | m, 0 => by simp [lucasNum_succ_succ]
  | m, 1 => by
    simp only [lucasNum_succ_succ, show Nat.fib 3 = 2 from rfl, show Nat.fib 2 = 1 from rfl]
    push_cast; ring
  | m, n + 2 => by
    -- L(m+n+4) = L(m+n+3) + L(m+n+2) by Lucas recurrence
    have h1 : lucasNum (m + (n + 2) + 2) = lucasNum (m + (n + 1) + 2) + lucasNum (m + n + 2) := by
      rw [show m + (n + 2) + 2 = (m + (n + 1) + 2) + 1 from by omega]; rfl
    push_cast [h1, lucasNum_add_formula m (n + 1), lucasNum_add_formula m n]
    -- F(n+4) = F(n+3) + F(n+2), F(n+3) = F(n+2) + F(n+1)
    have hf1 : (Nat.fib (n + 2 + 2) : ℤ) = Nat.fib (n + 2 + 1) + Nat.fib (n + 2) := by
      have := Nat.fib_add_two (n := n + 2); push_cast [this]; ring
    have hf2 : (Nat.fib (n + 2 + 1) : ℤ) = Nat.fib (n + 1 + 1) + Nat.fib (n + 1) := by
      have := Nat.fib_add_two (n := n + 1)
      rw [show n + 1 + 2 = n + 2 + 1 from by omega, show n + 1 + 1 = n + 1 + 1 from rfl] at this
      push_cast [this]; ring
    rw [hf1, hf2]; ring

/-- Lucas multiplication formula: L(m)·L(n) = L(m+n) + (-1)^n · L(m-n) for n ≤ m.
    bridge:lucas-multiplication-formula -/
theorem lucasNum_mul_formula : ∀ (m n : Nat), n ≤ m →
    (lucasNum m : ℤ) * lucasNum n =
    lucasNum (m + n) + (-1) ^ n * lucasNum (m - n)
  | m, 0, _ => by simp [lucasNum_zero]; ring
  | m, 1, hm => by
    simp only [lucasNum_one, pow_one]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    push_cast [lucasNum_succ_succ k]; ring
  | m, n + 2, hmn => by
    -- L(m) * L(n+2) = L(m) * (L(n+1) + L(n))
    have ih1 := lucasNum_mul_formula m (n + 1) (by omega)
    have ih0 := lucasNum_mul_formula m n (by omega)
    push_cast [lucasNum_succ_succ n] at *
    rw [mul_add, ih1, ih0]
    -- Need: L(m+n+2) = L(m+n+1) + L(m+n)
    have hL_add : (lucasNum (m + (n + 2)) : ℤ) =
        lucasNum (m + (n + 1)) + lucasNum (m + n) := by
      have := lucasNum_succ_succ (m + n)
      rw [show m + (n + 2) = m + n + 2 from by omega,
          show m + (n + 1) = m + n + 1 from by omega]
      push_cast [this]; ring
    -- Need: L(m-n) = L(m-n-1) + L(m-n-2), i.e., L(m-(n+2)) is defined via recurrence
    have hL_sub : (lucasNum (m - n) : ℤ) =
        lucasNum (m - (n + 1)) + lucasNum (m - (n + 2)) := by
      have h1 := lucasNum_succ_succ (m - (n + 2))
      rw [show m - (n + 2) + 2 = m - n from by omega,
          show m - (n + 2) + 1 = m - (n + 1) from by omega] at h1
      push_cast [h1]; ring
    rw [hL_add, hL_sub]
    have : (-1 : ℤ) ^ (n + 2) = (-1) ^ n := by ring
    rw [this]
    have : (-1 : ℤ) ^ (n + 1) = -((-1) ^ n) := by ring
    rw [this]
    ring

/-- Lucas odd-double: L(2n+1) = L(n)*L(n+1) - (-1)^n.
    bridge:lucas-odd-double -/
theorem lucasNum_double_odd (n : Nat) :
    (lucasNum (2 * n + 1) : ℤ) = (lucasNum n : ℤ) * lucasNum (n + 1) - (-1) ^ n := by
  have h := lucasNum_mul_formula (n + 1) n (by omega)
  simp only [lucasNum_one, show n + 1 + n = 2 * n + 1 from by omega,
    show n + 1 - n = 1 from by omega, Nat.cast_one, mul_one] at h
  linarith [mul_comm (lucasNum (n + 1) : ℤ) (lucasNum n : ℤ)]

/-- Lucas partial sum: Σ_{k=0}^n L(k) = L(n+2) - 1.
    bridge:lucas-partial-sum -/
theorem lucasNum_partial_sum (n : Nat) :
    ∑ k ∈ Finset.range (n + 1), lucasNum k = lucasNum (n + 2) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hrec : lucasNum (n + 1 + 2) = lucasNum (n + 2) + lucasNum (n + 1) := by
      rw [show n + 1 + 2 = (n + 2) + 1 from by omega]; rfl
    rw [hrec]
    have := lucasNum_pos (n + 2)
    omega

-- ══════════════════════════════════════════════════════════════
-- Phase 209: Lucas square sum
-- ══════════════════════════════════════════════════════════════

/-- L(n)*L(n+1) >= 2 for n >= 1. -/
private theorem lucasNum_mul_succ_ge_two : ∀ n : Nat, 1 ≤ n →
    2 ≤ lucasNum n * lucasNum (n + 1)
  | 1, _ => by simp [lucasNum_succ_succ]
  | n + 2, _ => by
    have h1 := lucasNum_pos (n + 2)
    have h2 := lucasNum_pos (n + 3)
    have : 1 ≤ lucasNum (n + 2) := h1
    have : 2 ≤ lucasNum (n + 3) := by
      rw [show n + 3 = (n + 1) + 1 + 1 from by omega, lucasNum_succ_succ]
      have := lucasNum_pos (n + 1 + 1)
      have := lucasNum_pos (n + 1)
      omega
    calc 2 ≤ 1 * 2 := by omega
      _ ≤ lucasNum (n + 2) * lucasNum (n + 2 + 1) := Nat.mul_le_mul ‹_› ‹_›

/-- Lucas square sum: Sigma_{k=1}^n L(k)^2 = L(n)*L(n+1) - 2.
    bridge:lucas-sq-sum -/
theorem lucasNum_sq_sum : ∀ (n : Nat), 1 ≤ n →
    ∑ k ∈ Finset.range n, lucasNum (k + 1) ^ 2 = lucasNum n * lucasNum (n + 1) - 2
  | 0, h => by omega
  | 1, _ => by simp [lucasNum_succ_succ]
  | n + 2, _ => by
    rw [Finset.sum_range_succ]
    -- Normalize n+1+1 to n+2 everywhere
    have hnorm : lucasNum (n + 1 + 1) = lucasNum (n + 2) := by congr 1
    rw [hnorm]
    rw [lucasNum_sq_sum (n + 1) (by omega), hnorm]
    -- Goal: L(n+1)*L(n+2) - 2 + L(n+2)^2 = L(n+2)*L(n+3) - 2
    have hrec : lucasNum (n + 2 + 1) = lucasNum (n + 2) + lucasNum (n + 1) := by
      rw [show n + 2 + 1 = (n + 1) + 1 + 1 from by omega]; rfl
    rw [hrec]
    have hge := lucasNum_mul_succ_ge_two (n + 1) (by omega)
    rw [hnorm] at hge
    -- Key: L(n+1)*L(n+2) - 2 + L(n+2)^2 = L(n+2)*(L(n+2)+L(n+1)) - 2
    -- Both sides equal L(n+1)*L(n+2) + L(n+2)^2 - 2
    have h1 : lucasNum (n + 1) * lucasNum (n + 2) - 2 + lucasNum (n + 2) ^ 2 =
        lucasNum (n + 1) * lucasNum (n + 2) + lucasNum (n + 2) ^ 2 - 2 := by omega
    have h2 : lucasNum (n + 2) * (lucasNum (n + 2) + lucasNum (n + 1)) - 2 =
        lucasNum (n + 1) * lucasNum (n + 2) + lucasNum (n + 2) ^ 2 - 2 := by
      rw [Nat.mul_add, sq]; ring_nf
    rw [h1, h2]

-- ══════════════════════════════════════════════════════════════
-- Phase 222: Lucas numbers strictly increasing
-- ══════════════════════════════════════════════════════════════

/-- Lucas numbers strictly increasing for n >= 1: L(n) < L(n+1).
    thm:pom-parry-limit-chain-explicit -/
theorem lucasNum_strict_mono (n : Nat) (hn : 1 ≤ n) : lucasNum n < lucasNum (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Goal: L(m+1) < L(m+2) = L(m+1) + L(m)
  rw [lucasNum_succ_succ]
  exact Nat.lt_add_of_pos_right (lucasNum_pos m)

-- ══════════════════════════════════════════════════════════════
-- Phase 223: Total closed paths = Lucas number
-- ══════════════════════════════════════════════════════════════

/-- Total closed paths of length m = A^m[0,0] + A^m[1,1] = L(m) (Lucas number).
    thm:pom-parry-limit-chain-explicit -/
theorem goldenMean_total_closed_paths (m : Nat) (hm : 1 ≤ m) :
    (Graph.goldenMeanAdjacency ^ m) 0 0 + (Graph.goldenMeanAdjacency ^ m) 1 1 =
      (lucasNum m : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Graph.goldenMeanAdjacency_pow_00, Graph.goldenMeanAdjacency_pow_11,
    lucasNum_eq_fib (k + 1) (by omega)]
  simp only [show k + 1 - 1 = k from by omega]
  push_cast; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 226: Lucas square identity (all n)
-- ══════════════════════════════════════════════════════════════

/-- L(n)² = 5·F(n)² + 4·(-1)^n in ℤ, for all n.
    thm:pom-parry-limit-chain-explicit -/
theorem lucasNum_sq_eq_int (n : Nat) :
    (lucasNum n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lucasNum_zero]
  · exact lucasNum_sq n hn

-- ══════════════════════════════════════════════════════════════
-- Phase 229: Lucas >= Fibonacci
-- ══════════════════════════════════════════════════════════════

/-- L_n >= F_n unconditionally. thm:pom-parry-limit-chain-explicit -/
theorem lucasNum_ge_fib (n : Nat) : Nat.fib n ≤ lucasNum n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      rw [Nat.fib_add_two, lucasNum_succ_succ, Nat.add_comm (lucasNum (n + 1))]
      exact Nat.add_le_add (ih n (by omega)) (ih (n + 1) (by omega))

-- ══════════════════════════════════════════════════════════════
-- Phase 232: Fib shifted fusion defect + Lucas mod p
-- ══════════════════════════════════════════════════════════════

/-- F(a+2)*F(b+2) = F(a+b+2) + F(a)*F(b).
    lem:pom-shifted-fib-fusion-defect-positive -/
theorem fib_shifted_fusion_defect (a b : Nat) :
    Nat.fib (a + 2) * Nat.fib (b + 2) = Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b := by
  -- From fib_add_formula(a+1, b): F(a+b+2) = F(a+2)*F(b+1) + F(a+1)*F(b)
  have hadd := fib_add_formula (a + 1) b
  rw [show a + 1 + b + 1 = a + b + 2 from by omega, show a + 1 + 1 = a + 2 from by omega] at hadd
  -- F(b+2) = F(b+1) + F(b), F(a+2) = F(a+1) + F(a)
  have hb := Nat.fib_add_two (n := b)
  have ha := Nat.fib_add_two (n := a)
  nlinarith

-- ══════════════════════════════════════════════════════════════
-- Phase 233: Fib determinant volume law + fusion defect cocycle
-- ══════════════════════════════════════════════════════════════

/-- F(a+2)*F(b+2) - F(a)*F(b) = F(a+b+2) in ℤ.
    cor:pom-fib-determinant-volume-law -/
theorem fib_determinant_volume_law (a b : Nat) :
    (Nat.fib (a + 2) : ℤ) * Nat.fib (b + 2) - (Nat.fib a : ℤ) * Nat.fib b =
    Nat.fib (a + b + 2) := by
  have := fib_shifted_fusion_defect a b; omega

/-- Fusion defect 2-cocycle: associativity consistency of ω(a,b)=F(a)*F(b).
    prop:pom-fusion-defect-2cocycle-identity -/
theorem fib_fusion_defect_cocycle (a b c : Nat) :
    Nat.fib a * Nat.fib b * Nat.fib (c + 2) + Nat.fib (a + b) * Nat.fib c =
    Nat.fib b * Nat.fib c * Nat.fib (a + 2) + Nat.fib (b + c) * Nat.fib a := by
  -- Work in ℤ to use ring reasoning
  suffices h : (Nat.fib a * Nat.fib b * Nat.fib (c + 2) + Nat.fib (a + b) * Nat.fib c : ℤ) =
      (Nat.fib b * Nat.fib c * Nat.fib (a + 2) + Nat.fib (b + c) * Nat.fib a : ℤ) by
    exact_mod_cast h
  -- Abbreviate
  set Fa := (Nat.fib a : ℤ); set Fa1 := (Nat.fib (a + 1) : ℤ)
  set Fb := (Nat.fib b : ℤ); set Fb1 := (Nat.fib (b + 1) : ℤ)
  set Fc := (Nat.fib c : ℤ); set Fc1 := (Nat.fib (c + 1) : ℤ)
  set Fab := (Nat.fib (a + b) : ℤ); set Fbc := (Nat.fib (b + c) : ℤ)
  -- Key lemma: from two expansions of F(a+b+c+1)
  have h1 := fib_add_formula a (b + c)
  have h2 := fib_add_formula (a + b) c
  have h3 := fib_add_formula a b
  have h4 := fib_add_formula b c
  rw [show a + (b + c) + 1 = a + b + c + 1 from by omega] at h1
  -- h1 = h2 gives: Fa1*F(b+c+1) + Fa*Fbc = F(a+b+1)*Fc1 + Fab*Fc
  -- Substituting h4 and h3:
  -- Fa1*(Fb1*Fc1 + Fb*Fc) + Fa*Fbc = (Fa1*Fb1 + Fa*Fb)*Fc1 + Fab*Fc
  -- Cancel Fa1*Fb1*Fc1: Fa1*Fb*Fc + Fa*Fbc = Fa*Fb*Fc1 + Fab*Fc
  -- From h1=h2 and h3,h4: derive the key identity
  -- h1: F(a+b+c+1) = Fa1*F(b+c+1) + Fa*Fbc
  -- h4: F(b+c+1) = Fb1*Fc1 + Fb*Fc
  -- So: F(a+b+c+1) = Fa1*(Fb1*Fc1 + Fb*Fc) + Fa*Fbc
  --                 = Fa1*Fb1*Fc1 + Fa1*Fb*Fc + Fa*Fbc
  -- h2: F(a+b+c+1) = F(a+b+1)*Fc1 + Fab*Fc
  -- h3: F(a+b+1) = Fa1*Fb1 + Fa*Fb
  -- So: F(a+b+c+1) = (Fa1*Fb1 + Fa*Fb)*Fc1 + Fab*Fc
  --                 = Fa1*Fb1*Fc1 + Fa*Fb*Fc1 + Fab*Fc
  -- Equating: Fa1*Fb*Fc + Fa*Fbc = Fa*Fb*Fc1 + Fab*Fc
  have haux : Fa1 * Fb * Fc + Fa * Fbc = Fa * Fb * Fc1 + Fab * Fc := by
    have eq1 : (Nat.fib (a + b + c + 1) : ℤ) =
        Fa1 * Fb1 * Fc1 + Fa1 * Fb * Fc + Fa * Fbc := by
      have := h1; have := h4; nlinarith
    have eq2 : (Nat.fib (a + b + c + 1) : ℤ) =
        Fa1 * Fb1 * Fc1 + Fa * Fb * Fc1 + Fab * Fc := by
      have := h2; have := h3; nlinarith
    linarith
  -- Target: Fa*Fb*F(c+2) + Fab*Fc = Fb*Fc*F(a+2) + Fbc*Fa
  -- Expand F(c+2) = Fc1+Fc, F(a+2) = Fa1+Fa
  have hc : (Nat.fib (c + 2) : ℤ) = Fc1 + Fc := by
    push_cast [Nat.fib_add_two]; ring
  have ha : (Nat.fib (a + 2) : ℤ) = Fa1 + Fa := by
    push_cast [Nat.fib_add_two]; ring
  rw [hc, ha]; nlinarith

/-- Paper package: fusion defect, determinant volume law, 2-cocycle.
    lem:pom-shifted-fib-fusion-defect-positive, cor:pom-fib-determinant-volume-law,
    prop:pom-fusion-defect-2cocycle-identity -/
theorem paper_pom_shifted_fusion_defect_package :
    (∀ a b : Nat, Nat.fib (a + 2) * Nat.fib (b + 2) =
      Nat.fib (a + b + 2) + Nat.fib a * Nat.fib b) ∧
    (∀ a b : Nat, (Nat.fib (a + 2) : ℤ) * Nat.fib (b + 2) - (Nat.fib a : ℤ) * Nat.fib b =
      Nat.fib (a + b + 2)) ∧
    (∀ a b c : Nat,
      Nat.fib a * Nat.fib b * Nat.fib (c + 2) + Nat.fib (a + b) * Nat.fib c =
      Nat.fib b * Nat.fib c * Nat.fib (a + 2) + Nat.fib (b + c) * Nat.fib a) :=
  ⟨fib_shifted_fusion_defect, fib_determinant_volume_law, fib_fusion_defect_cocycle⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 234: Fib strict supermultiplicativity
-- ══════════════════════════════════════════════════════════════

/-- F(a+2)*F(b+2) > F(a+b+2) when a,b ≥ 1.
    prop:pom-path-component-multiplicity-refinement-monotone-extrema -/
theorem fib_shifted_strict_supermul (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.fib (a + b + 2) < Nat.fib (a + 2) * Nat.fib (b + 2) := by
  have h := fib_shifted_fusion_defect a b
  have hpos : 0 < Nat.fib a * Nat.fib b :=
    Nat.mul_pos (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr (by omega))
  omega

/-- L(n) ≥ F(n+1) for n ≥ 1. Tight bound from L = F(n+1) + F(n-1).
    bridge:lucas-ge-fib-succ -/
theorem lucasNum_ge_fib_succ (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 1) ≤ lucasNum n := by
  rw [lucasNum_eq_fib n hn]; omega

-- ══════════════════════════════════════════════════════════════
-- Phase 238: Lucas-Fib cross identities
-- ══════════════════════════════════════════════════════════════

/-- L(m)*F(n) + L(n)*F(m) = 2*F(m+n) for m, n ≥ 1.
    Fundamental Lucas-Fibonacci cross product identity.
    bridge:lucas-fib-cross-sum -/
theorem lucasNum_fib_cross_sum (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    lucasNum m * Nat.fib n + lucasNum n * Nat.fib m = 2 * Nat.fib (m + n) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [show 1 + m' = m' + 1 from by omega, show 1 + n' = n' + 1 from by omega]
  rw [lucasNum_eq_fib (m' + 1) (by omega), lucasNum_eq_fib (n' + 1) (by omega)]
  simp only [show m' + 1 + 1 = m' + 2 from by omega, show m' + 1 - 1 = m' from by omega,
             show n' + 1 + 1 = n' + 2 from by omega, show n' + 1 - 1 = n' from by omega]
  -- LHS = (F(m'+2)+F(m'))*F(n'+1) + (F(n'+2)+F(n'))*F(m'+1)
  -- Nat.fib_add m' (n'+1): F(m'+n'+2) = F(m')*F(n'+1) + F(m'+1)*F(n'+2)
  have h1 := Nat.fib_add m' (n' + 1)
  rw [show m' + (n' + 1) + 1 = m' + n' + 2 from by omega,
      show n' + 1 + 1 = n' + 2 from by omega] at h1
  -- Nat.fib_add (m'+1) n': F(m'+n'+2) = F(m'+1)*F(n') + F(m'+2)*F(n'+1)
  have h2 := Nat.fib_add (m' + 1) n'
  rw [show m' + 1 + n' + 1 = m' + n' + 2 from by omega,
      show m' + 1 + 1 = m' + 2 from by omega] at h2
  rw [show m' + 1 + (n' + 1) = m' + n' + 2 from by omega]
  nlinarith

/-- L(m+n+1)*F(n+1) - L(n+1)*F(m+n+1) = 2*(-1)^n * F(m) in ℤ.
    bridge:lucas-fib-cross-diff -/
theorem lucasNum_fib_cross_diff (m n : Nat) :
    (lucasNum (m + n + 1) : ℤ) * Nat.fib (n + 1) -
    (lucasNum (n + 1) : ℤ) * Nat.fib (m + n + 1) =
    2 * (-1) ^ n * Nat.fib m := by
  rw [lucasNum_eq_fib (m + n + 1) (by omega), lucasNum_eq_fib (n + 1) (by omega)]
  simp only [show m + n + 1 + 1 = m + n + 2 from by omega,
             show m + n + 1 - 1 = m + n from by omega,
             show n + 1 + 1 = n + 2 from by omega,
             show n + 1 - 1 = n from by omega]
  push_cast
  -- Nat.fib_add m (n+1): F(m+n+2) = F(m)*F(n+1) + F(m+1)*F(n+2)
  have hadd1 := Nat.fib_add m n
  have hadd2 := Nat.fib_add m (n + 1)
  rw [show m + (n + 1) + 1 = m + n + 2 from by omega,
      show n + 1 + 1 = n + 2 from by omega] at hadd2
  -- Cassini: F(n+2)*F(n) - F(n+1)^2 = (-1)^(n+1)
  have hcas := Graph.fib_cassini (n + 1) (by omega)
  simp only [show n + 1 + 1 = n + 2 from by omega, show n + 1 - 1 = n from by omega] at hcas
  -- F(n+1)^2 - F(n)*F(n+2) = (-1)^n
  have key : (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * Nat.fib (n + 2) =
      (-1 : ℤ) ^ n := by
    have : (-1 : ℤ) ^ (n + 1) = (-1) ^ n * (-1) := pow_succ (-1) n
    linarith
  -- fib_add_two
  have hfn := Nat.fib_add_two (n := n)
  have hfmn := Nat.fib_add_two (n := m + n)
  push_cast at hadd1 hadd2 hfn hfmn ⊢
  nlinarith [key, sq_nonneg ((Nat.fib (n + 1) : ℤ))]

-- ══════════════════════════════════════════════════════════════
-- Phase R110: Lucas-Fibonacci gcd
-- ══════════════════════════════════════════════════════════════

/-- gcd(L(n), F(n)) | 2 for n ≥ 1.
    bridge:lucas-fib-gcd -/
theorem lucasNum_fib_gcd_dvd_two (n : Nat) (hn : 1 ≤ n) :
    Nat.gcd (lucasNum n) (Nat.fib n) ∣ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- L(m+1) = F(m+2) + F(m)
  have hL : lucasNum (m + 1) = Nat.fib (m + 2) + Nat.fib m := lucasNum_eq_fib_aux m
  -- F(m+2) = F(m) + F(m+1)
  have hF : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  -- So L(m+1) = F(m+1) + 2 * F(m)
  have hL2 : lucasNum (m + 1) = Nat.fib (m + 1) + 2 * Nat.fib m := by omega
  set d := Nat.gcd (lucasNum (m + 1)) (Nat.fib (m + 1))
  -- d | L(m+1) and d | F(m+1)
  have hd1 : d ∣ lucasNum (m + 1) := Nat.gcd_dvd_left _ _
  have hd2 : d ∣ Nat.fib (m + 1) := Nat.gcd_dvd_right _ _
  -- d | L(m+1) - F(m+1) = 2 * F(m)
  have hd3 : d ∣ 2 * Nat.fib m := by
    have hsub : d ∣ lucasNum (m + 1) - Nat.fib (m + 1) := Nat.dvd_sub hd1 hd2
    rwa [hL2, Nat.add_sub_cancel_left] at hsub
  -- Coprime (fib m) (fib (m+1)), so coprime d (fib m)
  have hcop : Nat.Coprime (Nat.fib m) (Nat.fib (m + 1)) := Nat.fib_coprime_fib_succ m
  have hcop_d : Nat.Coprime d (Nat.fib m) :=
    Nat.Coprime.coprime_dvd_left hd2 hcop.symm
  -- d | 2 * F(m) and coprime d (F(m)), so d | 2
  exact hcop_d.dvd_of_dvd_mul_right hd3

/-- 4 ∣ L(n) iff n ≡ 3 (mod 6).
    bridge:lucas-four-divisibility -/
theorem lucasNum_four_dvd (n : Nat) : 4 ∣ lucasNum n ↔ n % 6 = 3 := by
  -- L(n) mod 4 has period 6: 2,1,3,0,3,3,2,1,3,0,3,3,...
  -- Key: L(k+6) ≡ L(k) mod 4
  have hperiod : ∀ k, 4 ∣ lucasNum (k + 6) ↔ 4 ∣ lucasNum k := by
    intro k
    -- L(k+6) = 18*L(k+1) + 7*L(k) (by expanding recurrence 6 times)
    -- Actually: L(k+6) = L(k+5)+L(k+4) = ... = 18L(k+1)+7L(k) (not needed)
    -- Simpler: show L(k+6) - L(k) ≡ 0 mod 4
    -- L(k+2)=L(k+1)+L(k), L(k+3)=2L(k+1)+L(k), L(k+4)=3L(k+1)+2L(k),
    -- L(k+5)=5L(k+1)+3L(k), L(k+6)=8L(k+1)+5L(k)
    -- L(k+6)-L(k) = 8L(k+1)+4L(k) = 4(2L(k+1)+L(k))
    have h2 : lucasNum (k + 2) = lucasNum (k + 1) + lucasNum k := lucasNum_succ_succ k
    have h3 : lucasNum (k + 3) = lucasNum (k + 2) + lucasNum (k + 1) := lucasNum_succ_succ (k + 1)
    have h4 : lucasNum (k + 4) = lucasNum (k + 3) + lucasNum (k + 2) := lucasNum_succ_succ (k + 2)
    have h5 : lucasNum (k + 5) = lucasNum (k + 4) + lucasNum (k + 3) := lucasNum_succ_succ (k + 3)
    have h6 : lucasNum (k + 6) = lucasNum (k + 5) + lucasNum (k + 4) := lucasNum_succ_succ (k + 4)
    -- L(k+6) = 8*L(k+1) + 5*L(k), so L(k+6) - L(k) = 8*L(k+1) + 4*L(k)
    -- L(k+6) = L(k) + 4*(2*L(k+1)+L(k))
    have hexp : lucasNum (k + 6) = lucasNum k + 4 * (2 * lucasNum (k + 1) + lucasNum k) := by omega
    constructor
    · intro hd; rw [hexp] at hd; omega
    · intro hd; rw [hexp]; omega
  constructor
  · -- Forward: 4|L(n) → n%6=3
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro h
      match n with
      | 0 => exfalso; rw [lucasNum_zero] at h; omega
      | 1 => exfalso; rw [lucasNum_one] at h; omega
      | 2 => exfalso; rw [lucasNum_two] at h; omega
      | 3 => rfl
      | 4 => exfalso; rw [show lucasNum 4 = 7 from rfl] at h; omega
      | 5 => exfalso; rw [show lucasNum 5 = 11 from rfl] at h; omega
      | n + 6 =>
        have := ih n (by omega) ((hperiod n).mp h)
        omega
  · -- Backward: n%6=3 → 4|L(n)
    intro h
    -- Write n = 6*q + 3
    have ⟨q, hq⟩ : ∃ q, n = 6 * q + 3 := ⟨n / 6, by omega⟩
    subst hq
    induction q with
    | zero => rw [show lucasNum 3 = 4 from rfl]
    | succ j ih =>
      rw [show 6 * (j + 1) + 3 = (6 * j + 3) + 6 from by ring]
      exact (hperiod (6 * j + 3)).mpr (ih (by omega))

-- lucasNum_coprime_five deferred: needs pair-state tracking for L mod 5 period proof
-- bridge:lucas-five-coprimality

/-- gcd(L(n), F(n)) = 2 if 3|n, else 1.
    bridge:lucas-fib-gcd-exact -/
theorem lucasNum_fib_gcd_eq (n : Nat) :
    Nat.gcd (lucasNum n) (Nat.fib n) = if 3 ∣ n then 2 else 1 := by
  split
  · -- Case 3|n: both even, gcd ≥ 2, and gcd|2 so gcd = 2
    rename_i h3
    have hLeven : 2 ∣ lucasNum n := (lucasNum_even_iff n).mpr h3
    have hFeven : 2 ∣ Nat.fib n := (fib_even_iff_three_dvd n).mpr h3
    have hgcd_ge : 2 ∣ Nat.gcd (lucasNum n) (Nat.fib n) :=
      Nat.dvd_gcd hLeven hFeven
    cases n with
    | zero => simp [lucasNum_zero]
    | succ m =>
      have hgcd_le := lucasNum_fib_gcd_dvd_two (m + 1) (by omega)
      -- gcd ≥ 2 and gcd | 2, so gcd = 2
      exact Nat.dvd_antisymm hgcd_le hgcd_ge
  · -- Case ¬3|n: F(n) is odd, so gcd is odd, and gcd|2 forces gcd=1
    rename_i h3
    have hFodd : ¬ (2 ∣ Nat.fib n) := (fib_even_iff_three_dvd n).not.mpr h3
    -- gcd | F(n), so if gcd were even, F(n) would be even
    have hgcd_odd : ¬ (2 ∣ Nat.gcd (lucasNum n) (Nat.fib n)) := by
      intro h; exact hFodd (dvd_trans h (Nat.gcd_dvd_right _ _))
    cases n with
    | zero => exact absurd ⟨0, rfl⟩ h3
    | succ m =>
      have hgcd_le := lucasNum_fib_gcd_dvd_two (m + 1) (by omega)
      -- gcd | 2 and gcd is odd, so gcd ∈ {1, 2} and gcd ≠ 2, hence gcd = 1
      have : Nat.gcd (lucasNum (m + 1)) (Nat.fib (m + 1)) ∣ 2 := hgcd_le
      -- gcd | 2 means gcd ∈ {1, 2}. Since gcd is odd, gcd = 1.
      have hle : Nat.gcd (lucasNum (m + 1)) (Nat.fib (m + 1)) ≤ 2 := Nat.le_of_dvd (by omega) this
      have hpos : 0 < Nat.gcd (lucasNum (m + 1)) (Nat.fib (m + 1)) := Nat.pos_of_ne_zero (by
        intro h; rw [Nat.gcd_eq_zero_iff] at h; linarith [lucasNum_pos (m + 1)])
      omega

/-- Fibonacci-Lucas Wronskian: F(n)*L(n+1) - F(n+1)*L(n) = 2*(-1)^(n+1).
    bridge:fib-lucas-wronskian -/
theorem fib_lucas_wronskian (n : Nat) :
    (Nat.fib n : ℤ) * lucasNum (n + 1) - (Nat.fib (n + 1) : ℤ) * lucasNum n =
    2 * (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [lucasNum_zero, lucasNum_one]
  | succ k ih =>
    -- F(k+1)*L(k+2) - F(k+2)*L(k+1)
    -- = F(k+1)*(L(k+1)+L(k)) - (F(k+1)+F(k))*L(k+1)
    -- = F(k+1)*L(k) - F(k)*L(k+1) = -(F(k)*L(k+1)-F(k+1)*L(k)) = -IH = 2*(-1)^(k+2)
    have hfib := Nat.fib_add_two (n := k)
    push_cast [lucasNum_succ_succ (k), hfib]
    have hpow : (2 : ℤ) * (-1) ^ (k + 1 + 1) = -(2 * (-1) ^ (k + 1)) := by ring
    rw [hpow]; linarith

/-- Fibonacci tripling: F(3n) = F(n) * (5*F(n)^2 + 3*(-1)^n).
    bridge:fibonacci-tripling -/
theorem fib_tripling (n : Nat) :
    (Nat.fib (3 * n) : ℤ) = Nat.fib n * (5 * (Nat.fib n : ℤ) ^ 2 + 3 * (-1) ^ n) := by
  cases n with
  | zero => simp
  | succ m =>
    have hv := fib_vajda (m + 1) (m + 1) (m + 1)
    rw [show m + 1 + (m + 1) = 2 * (m + 1) from by omega] at hv
    rw [show 2 * (m + 1) + (m + 1) = 3 * (m + 1) from by omega] at hv
    have hlf := lucasNum_mul_fib (m + 1) (by omega)
    have hleq := lucasNum_eq_fib_aux m
    have hfib2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    have hLsq : (lucasNum (m + 1) : ℤ) ^ 2 =
        5 * (Nat.fib (m + 1) : ℤ) ^ 2 + 4 * (-1) ^ (m + 1) := by
      have hL : (lucasNum (m + 1) : ℤ) = Nat.fib (m + 2) + Nat.fib m := by linarith [hleq]
      have hF : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by linarith [hfib2]
      by_cases heven : Even m
      · have hcas := fib_cassini_even m heven
        have hpow : (-1 : ℤ) ^ (m + 1) = -1 := by
          have : Odd (m + 1) := Even.add_one heven
          exact Odd.neg_one_pow this
        rw [hpow]; push_cast at hcas; nlinarith [hL, hF]
      · have hcas := fib_cassini_odd m heven
        have hpow : (-1 : ℤ) ^ (m + 1) = 1 := by
          have hodd : Odd m := Nat.not_even_iff_odd.mp heven
          exact Even.neg_one_pow (Odd.add_one hodd)
        rw [hpow]; push_cast at hcas; nlinarith [hL, hF]
    -- Cast hlf to ℤ: L(k)*F(k) = F(2k)
    have hlfZ : (lucasNum (m + 1) : ℤ) * Nat.fib (m + 1) = Nat.fib (2 * (m + 1)) := by
      linarith [hlf]
    -- hv: F(2k)^2 - F(k)*F(3k) = (-1)^k * F(k)^2
    -- Substitute F(2k) = L(k)*F(k):
    -- (L(k)*F(k))^2 - F(k)*F(3k) = (-1)^k*F(k)^2
    -- L(k)^2*F(k)^2 - F(k)*F(3k) = (-1)^k*F(k)^2
    -- F(k)*(L(k)^2*F(k) - F(3k)) = (-1)^k*F(k)^2
    -- F(3k) = L(k)^2*F(k) - (-1)^k*F(k) = F(k)*(L(k)^2 - (-1)^k)
    -- = F(k)*(5F(k)^2 + 4(-1)^k - (-1)^k) = F(k)*(5F(k)^2 + 3(-1)^k)
    -- F(2k) = L(k)*F(k), so F(2k)^2 = L(k)^2*F(k)^2
    have hF2sq : (Nat.fib (2 * (m + 1)) : ℤ) ^ 2 =
        (lucasNum (m + 1) : ℤ) ^ 2 * (Nat.fib (m + 1) : ℤ) ^ 2 := by
      nlinarith [hlfZ]
    -- From hv: F(k)*F(3k) = F(2k)^2 - (-1)^k*F(k)^2
    have hprod : (Nat.fib (m + 1) : ℤ) * Nat.fib (3 * (m + 1)) =
        (Nat.fib (2 * (m + 1)) : ℤ) ^ 2 - (-1) ^ (m + 1) * (Nat.fib (m + 1) : ℤ) ^ 2 := by
      nlinarith [hv]
    -- Substitute F(2k)^2 = L(k)^2*F(k)^2 and L(k)^2 = 5F(k)^2+4(-1)^k:
    -- F(k)*F(3k) = (5F(k)^2+4(-1)^k)*F(k)^2 - (-1)^k*F(k)^2 = F(k)^2*(5F(k)^2+3(-1)^k)
    -- Divide by F(k) > 0:
    have hfpos : (Nat.fib (m + 1) : ℤ) ≠ 0 := by
      have := Nat.fib_pos.mpr (show 0 < m + 1 from by omega); omega
    have hmul : (Nat.fib (m + 1) : ℤ) * Nat.fib (3 * (m + 1)) =
        Nat.fib (m + 1) * (Nat.fib (m + 1) * (5 * (Nat.fib (m + 1) : ℤ) ^ 2 + 3 * (-1) ^ (m + 1))) := by
      rw [hprod, hF2sq, hLsq]; ring
    exact mul_left_cancel₀ hfpos hmul

/-- L(n)^2 + L(n+1)^2 = 5*F(2n+1).
    bridge:lucas-sq-pair-sum -/
theorem lucasNum_sq_pair_sum (n : Nat) :
    lucasNum n ^ 2 + lucasNum (n + 1) ^ 2 = 5 * Nat.fib (2 * n + 1) := by
  have h1 := lucas_sq_eq_five_fib_sq n
  have h2 := lucas_sq_eq_five_fib_sq (n + 1)
  have h3 := fib_sq_add_sq n
  -- h1: L(n)^2 = 5*F(n)^2 + 4*(-1)^n
  -- h2: L(n+1)^2 = 5*F(n+1)^2 + 4*(-1)^(n+1)
  -- Sum: 5*(F(n)^2+F(n+1)^2) + 4*((-1)^n+(-1)^(n+1)) = 5*F(2n+1) + 0
  -- since (-1)^n + (-1)^(n+1) = 0
  have hcancel : (-1 : ℤ) ^ n + (-1) ^ (n + 1) = 0 := by ring
  -- Cast h3 to ℤ
  have h3Z : (Nat.fib n : ℤ) ^ 2 + (Nat.fib (n + 1) : ℤ) ^ 2 = Nat.fib (2 * n + 1) := by
    have := h3; push_cast at this ⊢; linarith
  -- In Nat, L(n)^2+L(n+1)^2 ≥ 0 and equals a Nat, so we can work in ℤ
  suffices hsuff : (lucasNum n ^ 2 + lucasNum (n + 1) ^ 2 : ℤ) =
      5 * Nat.fib (2 * n + 1) from Nat.cast_injective hsuff
  linarith [h1, h2, h3Z, hcancel]

/-- Lucas tripling: L(3n) = L(n) * (L(n)^2 - 3*(-1)^n).
    bridge:lucas-tripling -/
theorem lucasNum_tripling (n : Nat) :
    (lucasNum (3 * n) : ℤ) = lucasNum n * ((lucasNum n : ℤ) ^ 2 - 3 * (-1) ^ n) := by
  -- Step 1: L(2n)*L(n) = L(3n) + (-1)^n*L(n) from lucasNum_mul_formula
  have hmul := lucasNum_mul_formula (2 * n) n (by omega)
  rw [show 2 * n + n = 3 * n from by omega, show 2 * n - n = n from by omega] at hmul
  -- hmul: L(2n)*L(n) = L(3n) + (-1)^n*L(n)
  -- Step 2: L(2n) = L(n)^2 - 2*(-1)^n
  have hdbl := lucasNum_double_uncond n
  -- Step 3: L(3n) = L(n)*L(2n) - (-1)^n*L(n) = L(n)*(L(2n)-(-1)^n)
  -- = L(n)*(L(n)^2-2(-1)^n-(-1)^n) = L(n)*(L(n)^2-3(-1)^n)
  -- L(3n) = L(n)*L(2n) - (-1)^n*L(n) (from hmul)
  -- = L(n)*(L(n)^2-2(-1)^n) - (-1)^n*L(n) (from hdbl)
  -- = L(n)^3 - 2(-1)^n*L(n) - (-1)^n*L(n)
  -- = L(n)^3 - 3(-1)^n*L(n) = L(n)*(L(n)^2 - 3(-1)^n)
  have key : (lucasNum (2 * n) : ℤ) * lucasNum n =
      (lucasNum n : ℤ) ^ 3 - 2 * (-1) ^ n * lucasNum n := by
    rw [hdbl]; ring
  nlinarith [key]

/-- Lucas-Cassini identity: L(n)^2 - L(n-1)*L(n+1) = 5*(-1)^n for n >= 1.
    prop:lucas-fibonacci-identity -/
theorem paper_lucas_cassini (n : Nat) (hn : 1 ≤ n) :
    (lucasNum n : ℤ) ^ 2 - (lucasNum (n - 1) : ℤ) * (lucasNum (n + 1) : ℤ) =
    5 * (-1) ^ n :=
  lucasNum_cassini n hn

/-- Lucas doubling: L(2n) = L(n)^2 - 2*(-1)^n for n >= 1.
    prop:fib-double-lucas -/
theorem paper_lucas_double (n : Nat) (hn : 1 ≤ n) :
    (lucasNum (2 * n) : ℤ) = (lucasNum n : ℤ) ^ 2 - 2 * (-1) ^ n :=
  lucasNum_double n hn

/-- L(n)^2 = 5*F(n)^2 + 4*(-1)^n (unconditional).
    prop:lucas-fibonacci-square-unconditional -/
theorem paper_lucas_five_fib_sq (n : Nat) :
    (lucasNum n : ℤ) ^ 2 = 5 * (Nat.fib n : ℤ) ^ 2 + 4 * (-1 : ℤ) ^ n :=
  lucas_sq_eq_five_fib_sq n

/-- Lucas-Fibonacci addition formula: L(m+n+2) = L(m+1)*F(n+2) + L(m)*F(n+1).
    thm:folding-stable-syntax-fib-fusion-ring -/
theorem paper_lucas_add_formula (m n : Nat) :
    (lucasNum (m + n + 2) : ℤ) =
    (lucasNum (m + 1) : ℤ) * (Nat.fib (n + 2) : ℤ) +
    (lucasNum m : ℤ) * (Nat.fib (n + 1) : ℤ) :=
  lucasNum_add_formula m n

/-- Lucas numbers strictly increasing for n >= 1: L(n) < L(n+1).
    thm:pom-parry-limit-chain-explicit -/
theorem paper_lucas_strict_mono (n : Nat) (hn : 1 ≤ n) : lucasNum n < lucasNum (n + 1) :=
  lucasNum_strict_mono n hn

/-- Paper: thm:pom-entropy-saturation (period-2 orbit) -/
theorem paper_shift_period2Seq : X.shiftN 2 X.period2Seq = X.period2Seq :=
  X.shiftN_two_period2

/-- Paper: thm:pom-entropy-saturation (period-2 not fixed) -/
theorem paper_shift_period2Seq_ne : X.shift X.period2Seq ≠ X.period2Seq :=
  X.shift_period2_ne

end Omega
