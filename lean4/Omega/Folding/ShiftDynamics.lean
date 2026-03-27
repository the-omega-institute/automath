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
    simp only [lucasNum_succ_succ, lucasNum_eq_fib_aux, fib_succ_succ']
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
  push_cast
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
    push_cast; exact_mod_cast Nat.fib_add_two
  nlinarith

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
      push_cast; exact_mod_cast lucasNum_succ_succ (k + 1)]
    rw [show k + 1 + 1 = k + 2 from by omega] at ih
    have ih' := ih (by omega)
    have hpow : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
    have hrec : (lucasNum (k + 2) : ℤ) = lucasNum (k + 1) + lucasNum k := by
      push_cast; exact_mod_cast lucasNum_succ_succ k
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
      have := @Nat.fib_add_two (k + 1); push_cast; linarith
    have hrec2 : (Nat.fib (k + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib k := by
      have := @Nat.fib_add_two k; push_cast; linarith
    have hpow : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
    have ih' := ih (by omega)
    rw [show k + 1 + 1 = k + 2 from by omega] at *
    rw [hrec1, hpow]; nlinarith

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
        have := @Nat.fib_add_two (k + 1); push_cast; linarith
      have hr2 : (Nat.fib (k + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib k := by
        have := @Nat.fib_add_two k; push_cast; linarith
      have hp : ((-1 : ℤ) ^ (k + 2) : ℤ) = -((-1) ^ (k + 1)) := by ring
      have ih' := ih (by omega)
      rw [show k + 1 + 1 = k + 2 from by omega] at *
      rw [hr1, hp]; nlinarith
  have hrec : (Nat.fib (m + 2) : ℤ) = Nat.fib (m + 1) + Nat.fib m := by
    have := @Nat.fib_add_two m; push_cast; linarith
  push_cast; nlinarith

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

/-- F(2n) = F(n)·L(n) for n ≥ 1.
    bridge:fib-double-lucas -/
theorem fib_double_eq_mul_lucas (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (2 * n) = Nat.fib n * lucasNum n := by
  have := lucasNum_mul_fib n hn; linarith [Nat.mul_comm (Nat.fib n) (lucasNum n)]

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
    have := Nat.fib_add_two (n := n); push_cast; linarith
  -- F(n+1)² - F(n)*F(n+2) = F(n+1)² - F(n)*(F(n)+F(n+1))
  -- = F(n+1)² - F(n)² - F(n)*F(n+1) = F(n+1)*(F(n+1)-F(n)) - F(n)²
  -- Need F(n-1) = F(n+1) - F(n), i.e., F(n+1) = F(n) + F(n-1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [show m + 1 - 1 = m from by omega, show m + 1 + 1 = m + 2 from by omega,
    show m + 1 + 2 = m + 3 from by omega] at *
  have hfib2 : (Nat.fib (m + 2) : ℤ) = Nat.fib m + Nat.fib (m + 1) := by
    have := Nat.fib_add_two (n := m); push_cast; linarith
  nlinarith

/-- F(n)·F(n+2) = F(n+1)² + (-1)^(n+1).
    bridge:fib-adjacent-product -/
theorem fib_adjacent_product (n : Nat) (hn : 1 ≤ n) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) = (Nat.fib (n + 1) : ℤ) ^ 2 + (-1) ^ (n + 1) := by
  have h := fib_succ_sq_sub_prod n hn
  have hpow : ((-1 : ℤ) ^ (n + 1)) = -((-1) ^ n) := by ring
  linarith

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

end Omega
