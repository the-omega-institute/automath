import Omega.Folding.MomentTriple
import Omega.Folding.Weight
import Omega.Core.Fib
import Omega.Folding.CCSPrime8Split
import Omega.Combinatorics.FibonacciCube
import Mathlib.Logic.Function.Basic

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 148: weight total sum
-- ══════════════════════════════════════════════════════════════

/-- For a fixed bit i : Fin m, |{w : Word m | w i = true}| = 2^{m-1}.
    bridge:card-true-at-bit -/
theorem card_true_at_bit (m : Nat) (hm : 1 ≤ m) (i : Fin m) :
    (Finset.univ.filter (fun w : Word m => w i = true)).card = 2 ^ (m - 1) := by
  -- Define involution: negate bit i
  set neg_i := fun (w : Word m) => Function.update w i (!w i) with neg_i_def
  -- neg_i is an involution
  have hinv : ∀ w : Word m, neg_i (neg_i w) = w := by
    intro w; ext j; simp only [neg_i_def]
    by_cases hj : j = i
    · subst hj; simp [Function.update_self, Bool.not_not]
    · simp [Function.update_of_ne hj]
  -- neg_i swaps true-set and false-set
  have hswap : ∀ w : Word m,
      w i = true ↔ neg_i w i = false := by
    intro w; simp [neg_i_def, Function.update_self]
  -- So |true-set| = |false-set|
  have hsize : (Finset.univ.filter (fun w : Word m => w i = true)).card =
      (Finset.univ.filter (fun w : Word m => w i = false)).card := by
    apply Finset.card_bij (fun w _ => neg_i w)
    · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact (hswap w).mp hw
    · intro w₁ _ w₂ _ h
      have := congr_arg neg_i h
      rwa [hinv, hinv] at this
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨neg_i w, by simp [Finset.mem_filter, (hswap (neg_i w)).mpr (by rw [hinv]; exact hw)],
        hinv w⟩
  -- |true-set| + |false-set| = 2^m
  have htotal : (Finset.univ.filter (fun w : Word m => w i = true)).card +
      (Finset.univ.filter (fun w : Word m => w i = false)).card = 2 ^ m := by
    rw [← Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_left]; intro w hw1 hw2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      exact absurd (hw1.symm.trans hw2) (by decide))]
    have : Finset.univ.filter (fun w : Word m => w i = true) ∪
        Finset.univ.filter (fun w : Word m => w i = false) = Finset.univ := by
      ext w; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => by cases w i <;> simp⟩
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp [pow_succ, mul_comm]
  linarith

/-- The total weight sum: Σ_w weight(w) = 2^{m-1} · (F_{m+3} - 2) for m ≥ 1.
    bridge:weight-total-sum -/
theorem weight_total_sum (m : Nat) (hm : 1 ≤ m) :
    ∑ w : Word m, weight w = 2 ^ (m - 1) * (Nat.fib (m + 3) - 2) := by
  simp_rw [weight_eq_fib_ite_sum]
  rw [Finset.sum_comm]
  simp_rw [show ∀ i : Fin m, (fun w : Word m => if w i then Nat.fib (i.val + 2) else 0) =
      (fun w => Nat.fib (i.val + 2) * if w i then 1 else 0) from
      fun i => by ext w; split_ifs <;> simp]
  simp_rw [← Finset.mul_sum]
  have hcount : ∀ i : Fin m,
      ∑ w : Word m, (if w i then (1 : Nat) else 0) = 2 ^ (m - 1) := by
    intro i
    change Finset.univ.sum _ = _
    rw [show (fun w : Word m => if w i then (1 : Nat) else 0) =
        (fun w => if w i = true then 1 else 0) from by ext w; simp]
    rw [Finset.sum_boole]
    exact_mod_cast card_true_at_bit m hm i
  simp_rw [hcount, ← Finset.sum_mul]
  rw [show ∑ i : Fin m, Nat.fib (i.val + 2) =
      ∑ i ∈ Finset.range m, Nat.fib (i + 2) from
    Fin.sum_univ_eq_sum_range (n := m) (fun i => Nat.fib (i + 2))]
  rw [fib_partial_sum_from_two, Nat.mul_comm]

-- ══════════════════════════════════════════════════════════════
-- Phase 149
-- ══════════════════════════════════════════════════════════════

-- exactWeightCount_symmetric already exists in MomentRecurrence.lean:551

/-- S_4 conditional recurrence: given the full recurrence as hypothesis,
    express S_4(m+5) as a subtraction.
    prop:pom-s4-recurrence -/
theorem momentSum_four_recurrence_sub_of
    (hrec : ∀ m, momentSum 4 (m + 5) + 2 * momentSum 4 m =
      2 * momentSum 4 (m + 4) + 7 * momentSum 4 (m + 3) + 2 * momentSum 4 (m + 1))
    (m : Nat) :
    momentSum 4 (m + 5) = 2 * momentSum 4 (m + 4) + 7 * momentSum 4 (m + 3) +
      2 * momentSum 4 (m + 1) - 2 * momentSum 4 m := by
  have := hrec m; omega

/-- EWT telescoping recurrence verified for m = 0..5.
    prop:pom-s3-recurrence -/
theorem exactWeightTriple_succ_bounded (m : Nat) (hm : m ≤ 5) :
    exactWeightTriple (m + 1) = 2 * exactWeightTriple m +
    3 * crossCorrSqHigh m + 3 * crossCorrSqLow m := by
  interval_cases m <;> native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 167
-- ══════════════════════════════════════════════════════════════

/-- Hidden bit count equals floor(2^m / 3). Discrete version of cor:pom-hidden-bit-entropy. -/
theorem hiddenBitCount_eq_div (m : Nat) :
    hiddenBitCount m = 2 ^ m / 3 := by
  have h := hiddenBitCount_closed m
  split_ifs at h with heven <;> omega

/-- Right-resolving: appending different bits to the same prefix always gives
    different Fold values. thm:pom-right-resolving. -/
theorem Fold_snoc_false_ne_true (v : Word m) :
    Fold (snoc v false) ≠ Fold (snoc v true) := by
  intro h
  have hsv := congrArg stableValue h
  rw [stableValue_Fold_snoc_false, stableValue_Fold_snoc_true] at hsv
  have hlt : weight v < Nat.fib (m + 3) := X.weight_lt_fib v
  rw [Nat.mod_eq_of_lt hlt] at hsv
  have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  by_cases hcase : weight v + Nat.fib (m + 2) < Nat.fib (m + 3)
  · rw [Nat.mod_eq_of_lt hcase] at hsv
    have : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
    omega
  · push_neg at hcase
    rw [Nat.mod_eq_sub_mod hcase, Nat.mod_eq_of_lt (by omega)] at hsv
    have : 0 < Nat.fib (m + 1) := Nat.fib_pos.mpr (by omega)
    omega

/-- S_3(m) is divisible by 4 for m ≥ 4. Consequence of S_3 recurrence.
    prop:pom-s3-recurrence -/
theorem momentSum_three_div_four (m : Nat) (hm : 4 ≤ m) :
    4 ∣ momentSum 3 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 => omega
    | 4 => exact ⟨22, by rw [momentSum_three_four]⟩
    | 5 => exact ⟨65, by rw [momentSum_three_five]⟩
    | 6 => exact ⟨205, by rw [momentSum_three_six]⟩
    | m + 7 =>
      have hrec := momentSum_three_recurrence (m + 4)
      rw [show (m + 4) + 3 = m + 7 from by omega,
          show (m + 4) + 2 = m + 6 from by omega,
          show (m + 4) + 1 = m + 5 from by omega] at hrec
      have ih4 := ih (m + 4) (by omega) (by omega)
      have ih5 := ih (m + 5) (by omega) (by omega)
      have ih6 := ih (m + 6) (by omega) (by omega)
      obtain ⟨a, ha⟩ := ih4
      obtain ⟨b, hb⟩ := ih5
      obtain ⟨c, hc⟩ := ih6
      rw [ha, hb, hc] at hrec
      exact ⟨2 * c + 4 * b - 2 * a, by omega⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 168
-- ══════════════════════════════════════════════════════════════

/-- S_3 growth rate upper bound: S_3(m+1) ≤ 4·S_3(m) for m ≥ 3.
    prop:pom-s3-recurrence -/
theorem momentSum_three_succ_le_quadruple (m : Nat) (hm : 3 ≤ m) :
    momentSum 3 (m + 1) ≤ 4 * momentSum 3 m := by
  match m with
  | 3 => rw [momentSum_three_four, momentSum_three_three]; omega
  | 4 => rw [momentSum_three_five, momentSum_three_four]; omega
  | m + 5 =>
    have hrec := momentSum_three_recurrence (m + 3)
    rw [show (m + 3) + 3 = m + 6 from by omega,
        show (m + 3) + 2 = m + 5 from by omega,
        show (m + 3) + 1 = m + 4 from by omega] at hrec
    have hdbl := momentSum_three_double (m + 4) (by omega)
    linarith

/-- 8 ∣ S_3(m) for m ≥ 7.
    prop:pom-s3-recurrence -/
theorem momentSum_three_mod_eight (m : Nat) (hm : 7 ≤ m) :
    8 ∣ momentSum 3 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => omega
    | 7 => exact ⟨313, by rw [momentSum_three_seven]⟩
    | 8 => exact ⟨971, by rw [momentSum_three_eight]⟩
    | 9 => exact ⟨2989, by rw [momentSum_three_nine]⟩
    | m + 10 =>
      have hrec := momentSum_three_recurrence (m + 7)
      rw [show (m + 7) + 3 = m + 10 from by omega,
          show (m + 7) + 2 = m + 9 from by omega,
          show (m + 7) + 1 = m + 8 from by omega] at hrec
      have ih7 := ih (m + 7) (by omega) (by omega)
      have ih8 := ih (m + 8) (by omega) (by omega)
      have ih9 := ih (m + 9) (by omega) (by omega)
      obtain ⟨a, ha⟩ := ih7
      obtain ⟨b, hb⟩ := ih8
      obtain ⟨c, hc⟩ := ih9
      rw [ha, hb, hc] at hrec
      exact ⟨2 * c + 4 * b - 2 * a, by omega⟩

/-- E00 doubling: E00(m+1) ≥ 2·E00(m) for all m.
    prop:pom-s2-plancherel -/
theorem exactWeightCollision_succ_ge_double (m : Nat) :
    2 * exactWeightCollision m ≤ exactWeightCollision (m + 1) := by
  match m with
  | 0 => native_decide
  | 1 => native_decide
  | m + 2 =>
    have hrec := exactWeightCollision_recurrence m
    have hmono := Nat.le_of_lt (exactWeightCollision_strict_mono m)
    linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 169
-- ══════════════════════════════════════════════════════════════

/-- Ratio monotonicity with gap: S_{a+1}(m) · S_b(m) ≤ S_a(m) · S_{b+1}(m) for a ≤ b.
    Follows from log-convexity by induction on b - a. -/
theorem momentSum_ratio_mono_gap (a b m : Nat) (hab : a ≤ b) :
    momentSum (a + 1) m * momentSum b m ≤
    momentSum a m * momentSum (b + 1) m := by
  induction b with
  | zero =>
    have : a = 0 := Nat.le_zero.mp hab
    subst this; exact le_of_eq (Nat.mul_comm _ _)
  | succ b ih =>
    by_cases hab' : a ≤ b
    · -- a ≤ b, so by IH: S_{a+1} · S_b ≤ S_a · S_{b+1}
      -- Also: S_{b+1}² ≤ S_b · S_{b+2} (log-convex)
      -- We want: S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- From IH: S_{a+1} · S_b ≤ S_a · S_{b+1}  ...(1)
      -- From log-convex: S_{b+1}² ≤ S_b · S_{b+2}  ...(2)
      -- From (1): S_{a+1} ≤ S_a · S_{b+1} / S_b (informally)
      -- Multiply (1) by S_{b+2} and (2) by S_a:
      -- S_{a+1} · S_b · S_{b+2} ≤ S_a · S_{b+1} · S_{b+2}
      -- S_a · S_{b+1}² ≤ S_a · S_b · S_{b+2}
      -- So S_{a+1} · S_{b+1} · S_b ≤ S_a · S_{b+1} · S_{b+2} (want)
      -- But we need: S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- Use: S_{a+1} · S_{b+1} · S_b ≤ S_a · S_{b+1} · S_{b+2} from (1)·S_{b+2} isn't right.
      -- Better: from (1) and (2), if S_b > 0:
      --   S_{a+1}/S_a ≤ S_{b+1}/S_b ≤ S_{b+2}/S_{b+1}
      -- So S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- Formal: cross-multiply chain.
      -- From IH: S_{a+1} · S_b ≤ S_a · S_{b+1}
      -- Multiply both sides by S_{b+2}: S_{a+1} · S_b · S_{b+2} ≤ S_a · S_{b+1} · S_{b+2}
      -- From log-convex: S_{b+1}² ≤ S_b · S_{b+2}, so S_{b+1} · S_{b+1} ≤ S_b · S_{b+2}
      -- Multiply both sides by S_a: S_a · S_{b+1}² ≤ S_a · S_b · S_{b+2}
      -- Combine: S_{a+1} · S_{b+1} · S_b ≤ S_a · S_{b+1} · S_{b+2} from first
      -- And    : S_a · S_{b+1} · S_{b+1} ≤ S_a · S_b · S_{b+2} from second
      -- Need:    S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- Multiply IH by S_{b+2}: S_{a+1} · S_b · S_{b+2} ≤ S_a · S_{b+1} · S_{b+2}   ...(*)
      -- From log-convex: S_{a+1} · S_{b+1}² ≤ S_{a+1} · S_b · S_{b+2}
      -- So S_{a+1} · S_{b+1}² ≤ S_a · S_{b+1} · S_{b+2}
      -- Divide by S_{b+1} (positive): S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      have hih := ih hab'
      have hlc := momentSum_ratio_mono b m
      have hpos := momentSum_pos' (b + 1) m
      -- hih: S_{a+1} · S_b ≤ S_a · S_{b+1}
      -- hlc: S_{b+1} · S_{b+1} ≤ S_b · S_{b+2}
      -- Want: S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- Equivalently: S_{a+1} · S_{b+1} · S_{b+1} ≤ S_a · S_{b+2} · S_{b+1}
      -- From hih · S_{b+2}: S_{a+1} · S_b · S_{b+2} ≤ S_a · S_{b+1} · S_{b+2}
      -- From hlc · S_{a+1}: S_{a+1} · S_{b+1}² ≤ S_{a+1} · S_b · S_{b+2}
      -- Chaining: S_{a+1} · S_{b+1}² ≤ S_a · S_{b+1} · S_{b+2}
      -- Cancel S_{b+1}: S_{a+1} · S_{b+1} ≤ S_a · S_{b+2}
      -- Chain: S_{a+1} · S_{b+1}² ≤ S_a · S_{b+2} · S_{b+1}
      -- From hlc · S_{a+1}: S_{a+1} · S_{b+1}² ≤ S_{a+1} · S_b · S_{b+2}
      -- From hih · S_{b+2}: S_{a+1} · S_b · S_{b+2} ≤ S_a · S_{b+1} · S_{b+2}
      -- Cancel S_{b+1}: done.
      suffices momentSum (a + 1) m * momentSum (b + 1) m * momentSum (b + 1) m ≤
          momentSum a m * momentSum (b + 1 + 1) m * momentSum (b + 1) m from
        Nat.le_of_mul_le_mul_right this hpos
      calc momentSum (a + 1) m * momentSum (b + 1) m * momentSum (b + 1) m
          = momentSum (a + 1) m * (momentSum (b + 1) m * momentSum (b + 1) m) := by ring
        _ ≤ momentSum (a + 1) m * (momentSum b m * momentSum (b + 2) m) :=
            Nat.mul_le_mul_left _ hlc
        _ = (momentSum (a + 1) m * momentSum b m) * momentSum (b + 2) m := by ring
        _ ≤ (momentSum a m * momentSum (b + 1) m) * momentSum (b + 2) m :=
            Nat.mul_le_mul_right _ hih
        _ = momentSum a m * momentSum (b + 1 + 1) m * momentSum (b + 1) m := by ring
    · -- a = b + 1
      push_neg at hab'
      have ha : a = b + 1 := by omega
      subst ha
      -- Goal: S_{b+2} · S_{b+1} ≤ S_{b+1} · S_{b+2}
      exact le_of_eq (Nat.mul_comm _ _)

/-- Generalized log-convexity: S_q(m)² ≤ S_{q-r}(m) · S_{q+r}(m).
    cor:pom-crossq-logconvex-chain. -/
theorem momentSum_log_convex_gap (q r m : Nat) (hr : r ≤ q) :
    momentSum q m ^ 2 ≤ momentSum (q - r) m * momentSum (q + r) m := by
  induction r with
  | zero => simp [sq]
  | succ r ih =>
    have hr' : r ≤ q := by omega
    have hih := ih hr'
    -- IH: S_q² ≤ S_{q-r} · S_{q+r}
    -- Want: S_q² ≤ S_{q-r-1} · S_{q+r+1}
    -- By ratio_mono_gap with a = q-r-1, b = q+r:
    --   S_{q-r} · S_{q+r} ≤ S_{q-r-1} · S_{q+r+1}
    have hkey : momentSum (q - r) m * momentSum (q + r) m ≤
        momentSum (q - (r + 1)) m * momentSum (q + (r + 1)) m := by
      have hqr : q - r = (q - (r + 1)) + 1 := by omega
      rw [hqr]
      exact momentSum_ratio_mono_gap (q - (r + 1)) (q + r) m (by omega)
    exact Nat.le_trans hih hkey

/-- n^q has the same parity as n for q ≥ 1. -/
private theorem Nat.pow_mod_two (n q : Nat) (hq : 1 ≤ q) :
    n ^ q % 2 = n % 2 := by
  induction q with
  | zero => omega
  | succ q ih =>
    rw [pow_succ, Nat.mul_mod]
    by_cases hq0 : q = 0
    · subst hq0; simp
    · rw [ih (by omega)]
      -- n % 2 * (n % 2) % 2 = n % 2
      have : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
      rcases this with h | h <;> simp [h]

/-- S_q(m) is even for q ≥ 1 and m ≥ 1. Generalizes momentSum_two_even and momentSum_three_even.
    Consequence of prop:pom-moment-congruence-q. -/
theorem momentSum_even (q m : Nat) (hq : 1 ≤ q) (hm : 1 ≤ m) :
    2 ∣ momentSum q m := by
  -- S_q = Σ d^q ≡ Σ d = 2^m ≡ 0 (mod 2)
  suffices h : momentSum q m % 2 = 0 from Nat.dvd_of_mod_eq_zero h
  simp only [momentSum]
  rw [Finset.sum_nat_mod]
  -- Replace d^q % 2 by d % 2 via pow_mod_two
  simp_rw [Nat.pow_mod_two _ _ hq]
  rw [← Finset.sum_nat_mod, X.fiberMultiplicity_sum_eq_pow]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [pow_succ]

/-- Prepend a bit to the left of a word. -/
def cons (b : Bool) (v : Word m) : Word (m + 1) :=
  Fin.cons b v

/-- Weight difference of cons true vs cons false is exactly 1. -/
theorem weight_cons_true_sub_false (v : Word m) :
    weight (cons true v) = weight (cons false v) + 1 := by
  simp only [weight_eq_fib_ite_sum, cons, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ite_false, Fin.val_zero, ite_true, Nat.zero_add,
    show Nat.fib (0 + 2) = 1 from by native_decide]
  -- Goal: 1 + rest = rest + 1
  omega

/-- Left-resolving: prepending different bits always gives different Fold values.
    thm:pom-left-resolving. -/
theorem Fold_cons_false_ne_true (v : Word m) :
    Fold (cons false v) ≠ Fold (cons true v) := by
  intro h
  -- cons false v, cons true v : Word (m+1), modulus is fib((m+1)+2) = fib(m+3)
  have hmod := (Fold_eq_iff_weight_mod (cons false v) (cons true v)).mp h
  have hdiff := weight_cons_true_sub_false v
  -- hmod uses fib((m+1)+2) = fib(m+3)
  -- weight(cons true v) = weight(cons false v) + 1
  rw [hdiff] at hmod
  -- hmod: w % fib(m+3) = (w+1) % fib(m+3) where w = weight(cons false v)
  have hfib_ge : 2 ≤ Nat.fib (m + 3) := by
    have h3 : Nat.fib 3 = 2 := by native_decide
    linarith [Nat.fib_mono (show 3 ≤ m + 3 by omega)]
  -- weight(cons true v) < fib(m+4): cons true v : Word (m+1)
  have hlt : weight (cons true v) < Nat.fib (m + 4) := X.weight_lt_fib (cons true v)
  -- So weight(cons false v) + 1 < fib(m+4), hence weight(cons false v) < fib(m+4) - 1
  rw [hdiff] at hlt
  -- Now: w % F = (w+1) % F with F = fib(m+3) ≥ 2 is impossible
  -- Proof: if w % F < F-1 then (w+1) % F = w % F + 1 ≠ w % F
  -- if w % F = F-1 then (w+1) % F = 0 ≠ F-1
  have hF := hfib_ge
  set w := weight (cons false v) with hw_def
  set F := Nat.fib (m + 3) with hF_def
  have hFpos : 0 < F := by omega
  have hwmod := Nat.mod_lt w hFpos
  by_cases hcase : w % F + 1 < F
  · -- w % F < F - 1, so (w+1) % F = w % F + 1
    have : (w + 1) % F = w % F + 1 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < F)]
      exact Nat.mod_eq_of_lt hcase
    omega
  · -- w % F = F - 1, so (w+1) % F = 0
    push_neg at hcase
    have heq : w % F = F - 1 := by omega
    have : (w + 1) % F = 0 := by
      rw [Nat.add_mod, heq]
      simp [Nat.sub_add_cancel (by omega : 1 ≤ F), Nat.mod_self]
    omega

/-- Biresolving: Fold is both right-resolving and left-resolving.
    con:pom-fold-biresolving.
    con:pom-fold-biresolving -/
theorem Fold_biresolving (v : Word m) :
    Fold (snoc v false) ≠ Fold (snoc v true) ∧
    Fold (cons false v) ≠ Fold (cons true v) :=
  ⟨Fold_snoc_false_ne_true v, Fold_cons_false_ne_true v⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 170
-- ══════════════════════════════════════════════════════════════

/-- Strict q-monotonicity: S_q(m) < S_{q+1}(m) for m ≥ 2 and q ≥ 1.
    prop:pom-moment-congruence-q -/
theorem momentSum_strict_mono_q (q m : Nat) (hq : 1 ≤ q) (hm : 2 ≤ m) :
    momentSum q m < momentSum (q + 1) m := by
  simp only [momentSum]
  -- Use Finset.sum_lt_sum: ∀ x, d^q ≤ d^{q+1}, and ∃ x₀, d^q < d^{q+1}
  apply Finset.sum_lt_sum
  · -- ∀ x, d(x)^q ≤ d(x)^{q+1} since d(x) ≥ 1
    intro x _
    exact Nat.pow_le_pow_right (X.fiberMultiplicity_pos x) (by omega)
  · -- ∃ x₀ with d(x₀) ≥ 2, so d(x₀)^q < d(x₀)^{q+1}
    obtain ⟨x₀, hx₀⟩ := exists_fiber_ge_two m hm
    exact ⟨x₀, Finset.mem_univ _, Nat.pow_lt_pow_right (by omega) (by omega)⟩

/-- Cauchy-Schwarz moment lower bound: (2^m)² ≤ F_{m+2} · S_2(m).
    prop:pom-power-sum-hankel-psd 2x2 principal minor. -/
theorem momentSum_two_cs_lower (m : Nat) :
    (2 ^ m) ^ 2 ≤ Nat.fib (m + 2) * momentSum 2 m :=
  momentSum_cauchy_schwarz m

-- ══════════════════════════════════════════════════════════════
-- Phase 171
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) strictly exceeds the type count F_{m+2} for m ≥ 2.
    prop:pom-moment-congruence-q -/
theorem momentSum_two_gt_fib (m : Nat) (hm : 2 ≤ m) :
    Nat.fib (m + 2) < momentSum 2 m := by
  rw [← X.card_eq_fib, ← Finset.card_univ]
  simp only [Finset.card_eq_sum_ones, momentSum]
  apply Finset.sum_lt_sum
  · intro x _
    exact Nat.one_le_pow 2 _ (X.fiberMultiplicity_pos x)
  · obtain ⟨x₀, hx₀⟩ := exists_fiber_ge_two m hm
    exact ⟨x₀, Finset.mem_univ _, by nlinarith [X.fiberMultiplicity_pos x₀]⟩

/-- D(m) < S_2(m) for m ≥ 2. Combines D² ≤ S_2 with D ≥ 2.
    prop:pom-power-sum-hankel-psd -/
theorem maxFiberMultiplicity_lt_momentSum_two (m : Nat) (hm : 2 ≤ m) :
    X.maxFiberMultiplicity m < momentSum 2 m := by
  have hD := maxFiberMultiplicity_ge_two m hm
  have hSq := maxFiberMultiplicity_sq_le_momentSum m
  nlinarith [hSq]

-- ══════════════════════════════════════════════════════════════
-- Phase 172
-- ══════════════════════════════════════════════════════════════

/-- Fiber count reciprocity: d(ofNat r) = d(ofNat (F_{m+1}-2-r)).
    prop:fold-fiber-count-reciprocity. -/
theorem fiberMultiplicity_value_symmetric (m r : Nat)
    (hr : r + Nat.fib (m + 2) ≤ Nat.fib (m + 3) - 2) :
    X.fiberMultiplicity (X.ofNat m r) =
    X.fiberMultiplicity (X.ofNat m (Nat.fib (m + 1) - 2 - r)) := by
  -- F_{m+3} = F_{m+1} + F_{m+2}
  have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  -- From hr: r ≤ F_{m+1} - 2
  have hr_le : r ≤ Nat.fib (m + 1) - 2 := by omega
  -- r < F_{m+2} (needed for stableValue_ofNat_lt)
  have hr_lt : r < Nat.fib (m + 2) := by
    have hle := Nat.fib_mono (show m + 1 ≤ m + 2 by omega)
    have hpos := fib_succ_pos m
    omega
  -- F_{m+1}-2-r < F_{m+2}
  have hr'_lt : Nat.fib (m + 1) - 2 - r < Nat.fib (m + 2) := by
    have hle := Nat.fib_mono (show m + 1 ≤ m + 2 by omega)
    have hpos := fib_succ_pos m
    omega
  -- stableValue (ofNat r) = r
  have hsv_r := X.stableValue_ofNat_lt r hr_lt
  -- stableValue (ofNat (F_{m+1}-2-r)) = F_{m+1}-2-r
  have hsv_r' := X.stableValue_ofNat_lt (Nat.fib (m + 1) - 2 - r) hr'_lt
  -- LHS = ewc(m,r) + ewc(m, r+F_{m+2})
  rw [fiberMultiplicity_eq_two_ewc, hsv_r]
  -- RHS = ewc(m, F_{m+1}-2-r) + ewc(m, (F_{m+1}-2-r)+F_{m+2})
  rw [fiberMultiplicity_eq_two_ewc, hsv_r']
  -- (F_{m+1}-2-r) + F_{m+2} = F_{m+3} - 2 - r
  have hfib_pos := fib_succ_pos m
  have hshift : Nat.fib (m + 1) - 2 - r + Nat.fib (m + 2) = Nat.fib (m + 3) - 2 - r := by
    omega
  rw [hshift]
  -- By exactWeightCount_symmetric:
  -- ewc(m, r) = ewc(m, F_{m+3}-2-r)
  have hsym1 := exactWeightCount_symmetric m r (by omega)
  -- ewc(m, r+F_{m+2}) = ewc(m, F_{m+3}-2-(r+F_{m+2})) = ewc(m, F_{m+1}-2-r)
  have hsym2 := exactWeightCount_symmetric m (r + Nat.fib (m + 2)) hr
  have hcomp : Nat.fib (m + 3) - 2 - (r + Nat.fib (m + 2)) = Nat.fib (m + 1) - 2 - r := by omega
  rw [hcomp] at hsym2
  -- LHS = ewc(r) + ewc(r+F) = ewc(F_{m+3}-2-r) + ewc(F_{m+1}-2-r)
  -- RHS = ewc(F_{m+1}-2-r) + ewc(F_{m+3}-2-r)
  omega

/-- S_q(m) > F_{m+2} for q ≥ 1 and m ≥ 2.
    prop:pom-moment-congruence-q -/
theorem momentSum_gt_fib (q m : Nat) (hq : 1 ≤ q) (hm : 2 ≤ m) :
    Nat.fib (m + 2) < momentSum q m := by
  rw [← X.card_eq_fib, ← Finset.card_univ]
  simp only [Finset.card_eq_sum_ones, momentSum]
  apply Finset.sum_lt_sum
  · intro x _
    exact Nat.one_le_pow q _ (X.fiberMultiplicity_pos x)
  · obtain ⟨x₀, hx₀⟩ := exists_fiber_ge_two m hm
    refine ⟨x₀, Finset.mem_univ _, ?_⟩
    have h2q : 2 ≤ X.fiberMultiplicity x₀ ^ q := by
      calc 2 ≤ X.fiberMultiplicity x₀ := hx₀
        _ = X.fiberMultiplicity x₀ ^ 1 := (pow_one _).symm
        _ ≤ X.fiberMultiplicity x₀ ^ q :=
            Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- D(m)^q ≤ S_q(m). -/
theorem maxFiberMultiplicity_pow_le_momentSum (q m : Nat) :
    X.maxFiberMultiplicity m ^ q ≤ momentSum q m := by
  obtain ⟨x₀, hx₀⟩ := X.maxFiberMultiplicity_achieved m
  simp only [momentSum]
  calc X.maxFiberMultiplicity m ^ q
      = X.fiberMultiplicity x₀ ^ q := by rw [hx₀]
    _ ≤ ∑ x : X m, X.fiberMultiplicity x ^ q :=
        Finset.single_le_sum (f := fun x => X.fiberMultiplicity x ^ q)
          (fun x _ => Nat.zero_le _) (Finset.mem_univ x₀)

/-- D(m) < S_q(m) for q ≥ 1 and m ≥ 2.
    prop:pom-power-sum-hankel-psd -/
theorem maxFiberMultiplicity_lt_momentSum (q m : Nat) (hq : 1 ≤ q) (hm : 2 ≤ m) :
    X.maxFiberMultiplicity m < momentSum q m := by
  have hD := maxFiberMultiplicity_ge_two m hm
  rcases q with _ | q
  · omega
  · cases q with
    | zero =>
      -- q = 1: D < 2^m = S_1
      rw [momentSum_one]
      exact maxFiber_lt_wordcount m hm
    | succ q =>
      -- q ≥ 2: D < D^{q+2} ≤ S_{q+2}
      have hpow := maxFiberMultiplicity_pow_le_momentSum (q + 2) m
      calc X.maxFiberMultiplicity m
          < X.maxFiberMultiplicity m ^ 2 := by nlinarith
        _ ≤ X.maxFiberMultiplicity m ^ (q + 2) :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ momentSum (q + 2) m := hpow

-- ══════════════════════════════════════════════════════════════
-- Phase 175
-- ══════════════════════════════════════════════════════════════


/-- Power mean lower bound: (2^m)^q ≤ F_{m+2}^{q-1} · S_q(m).
    Generalizes momentSum_two_cs_lower to all q ≥ 1.
    prop:pom-power-sum-hankel-psd -/
theorem momentSum_power_mean_lower (q m : Nat) (hq : 1 ≤ q) :
    (2 ^ m) ^ q ≤ Nat.fib (m + 2) ^ (q - 1) * momentSum q m := by
  -- Use pow_sum_le_card_mul_sum_pow: (Σ f)^{n+1} ≤ |s|^n * Σ f^{n+1}
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← momentSum_one m]
  simp only [momentSum, pow_one]
  rw [← X.card_eq_fib, ← Finset.card_univ (α := X m)]
  exact pow_sum_le_card_mul_sum_pow (fun _ _ => Nat.zero_le _) q

/-- Fiber readout at m ≥ 4 needs at least 2 binary query steps: 2^1 < D(m).
    prop:conclusion-index-torsion-time-lower-bound -/
theorem readout_needs_at_least_two_steps (m : Nat) (hm : 4 ≤ m) :
    2 ^ 1 < X.maxFiberMultiplicity m := by
  -- D(m) ≥ m/2 + 1 ≥ 3 > 2 = 2^1
  have := maxFiberMultiplicity_ge_half m
  simp; omega

-- ══════════════════════════════════════════════════════════════
-- Phase 176
-- ══════════════════════════════════════════════════════════════

/-- Folding the all-false word gives the zero stable word. -/
theorem Fold_allFalse (m : Nat) :
    Fold (fun (_ : Fin m) => false) = X.ofNat m 0 := by
  simp [Fold]

/-- stableValue of the all-false folded word is 0. -/
theorem stableValue_Fold_allFalse (m : Nat) :
    stableValue (Fold (fun (_ : Fin m) => false)) = 0 := by
  rw [Fold_allFalse]
  exact X.stableValue_ofNat_lt 0 (fib_succ_pos (m + 1))

/-- S_2(m) strictly exceeds 2^m for m ≥ 2: positive fiber variance.
    prop:pom-moment-congruence-q -/
theorem momentSum_two_sub_pow_pos (m : Nat) (hm : 2 ≤ m) :
    2 ^ m < momentSum 2 m := by
  rw [← momentSum_one m]
  exact momentSum_strict_mono_q 1 m (by omega) hm


-- ══════════════════════════════════════════════════════════════
-- Phase 178
-- ══════════════════════════════════════════════════════════════

/-- E00(m) ≥ m + 1: exact weight collision grows at least linearly.
    prop:pom-s2-plancherel -/
theorem exactWeightCollision_ge_succ (m : Nat) :
    m + 1 ≤ exactWeightCollision m := by
  rw [exactWeightCollision_eq_sum]
  -- E00(m) = 1 + Σ_{k<m} S_2(k). Each S_2(k) ≥ 1 by momentSum_pos'.
  have : m ≤ ∑ k ∈ Finset.range m, momentSum 2 k := by
    calc m = ∑ _k ∈ Finset.range m, 1 := by simp
      _ ≤ ∑ k ∈ Finset.range m, momentSum 2 k :=
          Finset.sum_le_sum fun k _ => momentSum_pos' 2 k
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 179
-- ══════════════════════════════════════════════════════════════

/-- E00(m) ≥ 2 · hiddenBitCount(m) for m ≥ 2.
    thm:pom-hidden-bit-count -/
theorem exactWeightCollision_ge_double_hiddenBitCount (m : Nat) (hm : 2 ≤ m) :
    2 * hiddenBitCount m ≤ exactWeightCollision m := by
  rw [hiddenBitCount_eq_div]
  -- E00(m) = 1 + Σ S_2(k) ≥ 1 + Σ 2^k. Use: each S_2(k) ≥ 2^k.
  have hE := exactWeightCollision_eq_sum m
  have hge : ∑ k ∈ Finset.range m, 2 ^ k ≤ ∑ k ∈ Finset.range m, momentSum 2 k :=
    Finset.sum_le_sum fun k _ => momentSum_two_ge_pow k
  -- Σ_{k<m} 2^k + 1 ≥ 2^m
  have hgeom : 2 ^ m ≤ 1 + ∑ k ∈ Finset.range m, 2 ^ k := by
    suffices h : ∀ n, 2 ^ n ≤ 1 + ∑ k ∈ Finset.range n, 2 ^ k from h m
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      rw [Finset.sum_range_succ, pow_succ]; linarith
  -- So E00(m) ≥ 2^m. And 2*(2^m/3) ≤ 2^m.
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 181
-- ══════════════════════════════════════════════════════════════

/-- S_2 base values strictly increasing through m = 0..7.
    prop:pom-s2-recurrence -/
theorem momentSum_two_strict_increasing_base :
    momentSum 2 0 < momentSum 2 1 ∧
    momentSum 2 1 < momentSum 2 2 ∧
    momentSum 2 2 < momentSum 2 3 ∧
    momentSum 2 3 < momentSum 2 4 ∧
    momentSum 2 4 < momentSum 2 5 ∧
    momentSum 2 5 < momentSum 2 6 ∧
    momentSum 2 6 < momentSum 2 7 := by
  rw [momentSum_two_zero, momentSum_two_one, momentSum_two_two, momentSum_two_three,
      momentSum_two_four, momentSum_two_five, momentSum_two_six, momentSum_two_seven]
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 182
-- ══════════════════════════════════════════════════════════════

/-- The image of Fold has cardinality F_{m+2}. -/
theorem Fold_image_card (m : Nat) :
    (Finset.univ.image (Fold (m := m))).card = Nat.fib (m + 2) := by
  rw [Finset.image_univ_of_surjective (Fold_surjective m),
      Finset.card_univ, X.card_eq_fib]

/-- S_3 base values strictly increasing through m = 0..7.
    prop:pom-s3-recurrence -/
theorem momentSum_three_strict_increasing_base :
    momentSum 3 0 < momentSum 3 1 ∧
    momentSum 3 1 < momentSum 3 2 ∧
    momentSum 3 2 < momentSum 3 3 ∧
    momentSum 3 3 < momentSum 3 4 ∧
    momentSum 3 4 < momentSum 3 5 ∧
    momentSum 3 5 < momentSum 3 6 ∧
    momentSum 3 6 < momentSum 3 7 := by
  rw [momentSum_three_zero, momentSum_three_one, momentSum_three_two,
      momentSum_three_three, momentSum_three_four, momentSum_three_five,
      momentSum_three_six, momentSum_three_seven]
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 183
-- ══════════════════════════════════════════════════════════════

/-- S_4 base values strictly increasing through m = 0..6.
    prop:pom-s4-recurrence -/
theorem momentSum_four_strict_increasing_base :
    momentSum 4 0 < momentSum 4 1 ∧
    momentSum 4 1 < momentSum 4 2 ∧
    momentSum 4 2 < momentSum 4 3 ∧
    momentSum 4 3 < momentSum 4 4 ∧
    momentSum 4 4 < momentSum 4 5 ∧
    momentSum 4 5 < momentSum 4 6 := by
  rw [momentSum_four_zero, momentSum_four_one, momentSum_four_two,
      momentSum_four_three, momentSum_four_four, momentSum_four_five,
      momentSum_four_six]
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 184
-- ══════════════════════════════════════════════════════════════

/-- E00(m) > 0 for all m. -/
theorem exactWeightCollision_pos (m : Nat) : 0 < exactWeightCollision m := by
  have := exactWeightCollision_ge_succ m; omega

-- ══════════════════════════════════════════════════════════════
-- Phase 187
-- ══════════════════════════════════════════════════════════════

/-- S_2² ≤ S_1·S_3 verified for m=0,2,4,6.
    cor:pom-crossq-logconvex-chain -/
theorem momentSum_log_convex_audit_base :
    momentSum 2 0 ^ 2 ≤ momentSum 1 0 * momentSum 3 0 ∧
    momentSum 2 2 ^ 2 ≤ momentSum 1 2 * momentSum 3 2 ∧
    momentSum 2 4 ^ 2 ≤ momentSum 1 4 * momentSum 3 4 ∧
    momentSum 2 6 ^ 2 ≤ momentSum 1 6 * momentSum 3 6 := by
  simp only [momentSum_two_zero, momentSum_two_two, momentSum_two_four, momentSum_two_six,
    momentSum_one, momentSum_three_zero, momentSum_three_two, momentSum_three_four,
    momentSum_three_six]
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 213: Cross-order moment inequality
-- ══════════════════════════════════════════════════════════════

/-- Cross-order moment inequality: (2^m)^q ≤ S_q(m) * F(m+2)^(q-1) for q≥1.
    prop:pom-crossq-g-monotone -/
theorem momentSum_crossq_from_base (q m : Nat) (hq : 1 ≤ q) :
    (2 ^ m) ^ q ≤ momentSum q m * Nat.fib (m + 2) ^ (q - 1) := by
  have := momentSum_power_mean_lower q m hq
  linarith [Nat.mul_comm (Nat.fib (m + 2) ^ (q - 1)) (momentSum q m)]

-- ══════════════════════════════════════════════════════════════
-- Phase 217: S_4 strict monotonicity (extended base)
-- ══════════════════════════════════════════════════════════════

theorem momentSum_four_seven : momentSum 4 7 = 12208 := by
  rw [← cMomentSum_eq]; native_decide
theorem momentSum_four_eight : momentSum 4 8 = 47480 := by
  rw [← cMomentSum_eq]; native_decide
theorem momentSum_four_nine : momentSum 4 9 = 181576 := by
  rw [← cMomentSum_eq]; native_decide
theorem momentSum_four_ten : momentSum 4 10 = 700384 := by
  rw [← cMomentSum_eq]; native_decide

/-- S_4 is strictly increasing for 2 ≤ m ≤ 9. prop:pom-s4-recurrence -/
theorem momentSum_four_strict_mono (m : Nat) (hm : 2 ≤ m) (hm' : m ≤ 9) :
    momentSum 4 m < momentSum 4 (m + 1) := by
  have h23 : momentSum 4 2 < momentSum 4 3 := by
    rw [momentSum_four_two, momentSum_four_three]; omega
  have h34 : momentSum 4 3 < momentSum 4 4 := by
    rw [momentSum_four_three, momentSum_four_four]; omega
  have h45 : momentSum 4 4 < momentSum 4 5 := by
    rw [momentSum_four_four, momentSum_four_five]; omega
  have h56 : momentSum 4 5 < momentSum 4 6 := by
    rw [momentSum_four_five, momentSum_four_six]; omega
  have h67 : momentSum 4 6 < momentSum 4 7 := by
    rw [momentSum_four_six, momentSum_four_seven]; omega
  have h78 : momentSum 4 7 < momentSum 4 8 := by
    rw [momentSum_four_seven, momentSum_four_eight]; omega
  have h89 : momentSum 4 8 < momentSum 4 9 := by
    rw [momentSum_four_eight, momentSum_four_nine]; omega
  have h910 : momentSum 4 9 < momentSum 4 10 := by
    rw [momentSum_four_nine, momentSum_four_ten]; omega
  interval_cases m <;> assumption

-- ══════════════════════════════════════════════════════════════
-- Phase 218: S_2(m)^q ≤ S_{2q}(m) · F(m+2)^{q-1}
-- ══════════════════════════════════════════════════════════════

/-- S_2(m)^q ≤ S_{2q}(m) · F(m+2)^{q-1}. By power mean inequality applied to
    f(x) = d_m(x)^2 over the Fibonacci cube X_m.
    prop:pom-sq-quasi-multiplicative -/
theorem momentSum_two_pow_le (q m : Nat) (hq : 1 ≤ q) :
    momentSum 2 m ^ q ≤ momentSum (2 * q) m * Nat.fib (m + 2) ^ (q - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  simp only [momentSum]
  rw [← X.card_eq_fib, ← Finset.card_univ (α := X m)]
  have key : ∀ x ∈ (Finset.univ : Finset (X m)), 0 ≤ X.fiberMultiplicity x ^ 2 :=
    fun _ _ => Nat.zero_le _
  have h := pow_sum_le_card_mul_sum_pow key q
  simp_rw [show ∀ x : X m, (X.fiberMultiplicity x ^ 2) ^ (q + 1) =
    X.fiberMultiplicity x ^ (2 * (q + 1)) from
    fun x => by rw [← pow_mul]] at h
  rw [Nat.mul_comm] at h
  exact h

-- ══════════════════════════════════════════════════════════════
-- Phase 226: S_2 strict doubling
-- ══════════════════════════════════════════════════════════════

/-- S_2(m+1) > 2*S_2(m) for m ≥ 2. prop:pom-s2-recurrence -/
theorem momentSum_two_succ_gt_double (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 2 m < momentSum 2 (m + 1) := by
  -- Base cases m=2,3,4 by values, then induction using the 3-step recurrence.
  -- Recurrence: S_2(m+3) = 2*S_2(m+2) + 2*S_2(m+1) - 2*S_2(m)
  -- So S_2(m+3) > 2*S_2(m+2) ⟺ 2*S_2(m+1) > 2*S_2(m) ⟺ S_2(m+1) > S_2(m),
  -- which follows from IH since 2*S_2(m) < S_2(m+1) implies S_2(m) < S_2(m+1).
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 => omega
    | 2 => rw [momentSum_two_two, momentSum_two_three]; omega
    | 3 => rw [momentSum_two_three, momentSum_two_four]; omega
    | 4 => rw [momentSum_two_four, momentSum_two_five]; omega
    | m + 5 =>
      -- Use recurrence for m+3: S_2(m+6) + 2*S_2(m+3) = 2*S_2(m+5) + 2*S_2(m+4)
      have hrec := momentSum_two_recurrence (m + 3)
      -- IH at m+3: 2*S_2(m+3) < S_2(m+4)
      have h3 := ih (m + 3) (by omega) (by omega)
      -- IH at m+4: 2*S_2(m+4) < S_2(m+5)
      have h4 := ih (m + 4) (by omega) (by omega)
      -- From hrec: S_2(m+6) = 2*S_2(m+5) + 2*S_2(m+4) - 2*S_2(m+3)
      -- Need: 2*S_2(m+5) < S_2(m+6), i.e., 2*(S_2(m+4) - S_2(m+3)) > 0
      -- From h3: S_2(m+4) > 2*S_2(m+3) > S_2(m+3)
      linarith

-- ══════════════════════════════════════════════════════════════
-- Phase 242: Markov bound for large fibers
-- ══════════════════════════════════════════════════════════════

/-- D^q * |{x : d(x) ≥ D}| ≤ S_q(m) — Markov bound for large fibers.
    prop:fold-large-fiber-moment-upperbounds -/
theorem paper_large_fiber_moment_bound (q m D : Nat) (hD : 1 ≤ D) (hq : 1 ≤ q) :
    D ^ q * (Finset.univ.filter (fun x : X m => D ≤ X.fiberMultiplicity x)).card
    ≤ momentSum q m := by
  unfold momentSum
  set S := Finset.univ.filter (fun x : X m => D ≤ X.fiberMultiplicity x)
  have h1 : D ^ q * S.card = S.sum (fun _ => D ^ q) := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have h2 : S.sum (fun _ => D ^ q) ≤ S.sum (fun x => X.fiberMultiplicity x ^ q) := by
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Nat.pow_le_pow_left hx.2 q
  have h3 : S.sum (fun x => X.fiberMultiplicity x ^ q) ≤
      ∑ x : X m, X.fiberMultiplicity x ^ q := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.filter_subset _ _
  linarith

-- ══════════════════════════════════════════════════════════════
-- Phase R2: Cauchy-Schwarz lower bound, S_3 strict mono, D < 2^m
-- ══════════════════════════════════════════════════════════════

/-- S_2(m) * F_{m+2} ≥ (2^m)², discrete Cauchy-Schwarz lower bound.
    thm:fold-collision-convex-lower-bounds -/
theorem momentSum_two_ge_spike_flat (m : Nat) :
    momentSum 2 m * Nat.fib (m + 2) ≥ (2 ^ m) ^ 2 := by
  -- Cauchy-Schwarz: (∑ f)² ≤ |S| * ∑ f²
  have hCS : (∑ x ∈ (Finset.univ : Finset (X m)), (X.fiberMultiplicity x : Nat)) ^ 2 ≤
      (Finset.univ : Finset (X m)).card *
      ∑ x ∈ (Finset.univ : Finset (X m)), (X.fiberMultiplicity x : Nat) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, X.card_eq_fib] at hCS
  rw [show ∑ x ∈ (Finset.univ : Finset (X m)), X.fiberMultiplicity x = 2 ^ m from by
    simp [X.fiberMultiplicity_sum_eq_pow]] at hCS
  rw [show ∑ x ∈ (Finset.univ : Finset (X m)), X.fiberMultiplicity x ^ 2 = momentSum 2 m from by
    simp [momentSum]] at hCS
  linarith [Nat.mul_comm (momentSum 2 m) (Nat.fib (m + 2))]

/-- S_3(m) < S_3(m+1) for all m.
    prop:pom-s3-recurrence -/
theorem momentSum_three_strict_mono_all (m : Nat) :
    momentSum 3 m < momentSum 3 (m + 1) := by
  match m with
  | 0 => rw [momentSum_three_zero, momentSum_three_one]; omega
  | m + 1 => exact momentSum_three_strict_mono (m + 1) (by omega)

/-- D(m) < 2^m for m ≥ 2.
    cor:pom-max-fiber-rate-endpoint -/
theorem maxFiberMultiplicity_strict_lt_pow (m : Nat) (hm : 2 ≤ m) :
    X.maxFiberMultiplicity m < 2 ^ m :=
  maxFiber_lt_wordcount m hm

end Omega
