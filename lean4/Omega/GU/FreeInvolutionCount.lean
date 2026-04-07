import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace Omega.GU

def freeInvolutionCount (r : Nat) : Nat := (2 * r).factorial / (2 ^ r * r.factorial)

/-- There is no fixed-point-free involution on an odd finite set.
    thm:fiberwise-free-involution-matching-entropy -/
theorem no_free_involution_on_odd (k : Nat) :
    ¬ ∃ f : Fin (2 * k + 1) → Fin (2 * k + 1), Function.Bijective f ∧
        (∀ x, f (f x) = x) ∧ (∀ x, f x ≠ x) := by
  classical
  intro h
  rcases h with ⟨f, _hfbij, hinv, hfree⟩
  let σ : Equiv.Perm (Fin (2 * k + 1)) := Function.Involutive.toPerm f hinv
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two, σ] using congrArg Fin.val (hinv x)
  have hσ : σ ^ (2 ^ 1) = 1 := by
    simpa using hσ2
  have hnotEven : ¬ Even (Fintype.card (Fin (2 * k + 1))) := by
    simp [Fintype.card_fin]
  have hcard : ¬ 2 ∣ Fintype.card (Fin (2 * k + 1)) := by
    exact fun h => hnotEven ((even_iff_two_dvd).2 h)
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard hσ
  exact hfree a ha

/-- Closed-form normalization of the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_formula (r : Nat) :
    freeInvolutionCount r * (2 ^ r * r.factorial) = (2 * r).factorial := by
  unfold freeInvolutionCount
  have hdiv : 2 ^ r * r.factorial ∣ (2 * r).factorial := by
    cases r with
    | zero => simp
    | succ r =>
        refine ⟨Nat.doubleFactorial (2 * r + 1), ?_⟩
        rw [show 2 * (r + 1) = 2 * r + 2 by ring]
        rw [show (2 * r + 2).factorial =
          Nat.doubleFactorial (2 * r + 2) * Nat.doubleFactorial (2 * r + 1) by
          simpa using (Nat.factorial_eq_mul_doubleFactorial (2 * r + 1))]
        rw [show 2 * r + 2 = 2 * (r + 1) by ring]
        rw [Nat.doubleFactorial_two_mul]
  simpa [mul_assoc, mul_left_comm, mul_comm] using Nat.div_mul_cancel hdiv

/-- Recurrence for the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_succ (r : Nat) :
    freeInvolutionCount (r + 1) = (2 * r + 1) * freeInvolutionCount r := by
  have hpos : 0 < 2 ^ (r + 1) * (r + 1).factorial := by
    positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    freeInvolutionCount (r + 1) * (2 ^ (r + 1) * (r + 1).factorial)
        = (2 * (r + 1)).factorial := freeInvolutionCount_formula (r + 1)
    _ = (2 * r + 2) * ((2 * r + 1) * (2 * r).factorial) := by
          rw [show 2 * (r + 1) = 2 * r + 2 by ring]
          rw [Nat.factorial_succ, Nat.factorial_succ]
    _ = (2 * r + 2) * ((2 * r + 1) * (freeInvolutionCount r * (2 ^ r * r.factorial))) := by
          rw [freeInvolutionCount_formula r]
    _ = ((2 * r + 1) * freeInvolutionCount r) * ((2 * r + 2) * (2 ^ r * r.factorial)) := by
          ring
    _ = ((2 * r + 1) * freeInvolutionCount r) * (2 ^ (r + 1) * (r + 1).factorial) := by
          rw [show 2 ^ (r + 1) * (r + 1).factorial = (2 * r + 2) * (2 ^ r * r.factorial) by
            rw [pow_succ, Nat.factorial_succ]
            ring]

/-- Product formula for the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_eq_prod_odds (r : Nat) :
    freeInvolutionCount r = ∏ i ∈ Finset.range r, (2 * i + 1) := by
  induction r with
  | zero => simp [freeInvolutionCount]
  | succ r ihr =>
      rw [freeInvolutionCount_succ, Finset.prod_range_succ, ihr, mul_comm]

/-- Double-factorial form of the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_eq_doubleFactorial (r : Nat) :
    freeInvolutionCount r = Nat.doubleFactorial (2 * r - 1) := by
  induction r with
  | zero => simp [freeInvolutionCount]
  | succ r ihr =>
      rw [freeInvolutionCount_succ, ihr]
      simpa [two_mul, add_assoc, add_comm, add_left_comm] using
        (Nat.doubleFactorial_add_one (2 * r)).symm

/-- Small values of the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_small :
    freeInvolutionCount 1 = 1 ∧ freeInvolutionCount 2 = 3 ∧ freeInvolutionCount 3 = 15 := by
  native_decide

/-- The free involution count is positive for r ≥ 1.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_pos (r : Nat) (hr : 1 ≤ r) :
    0 < freeInvolutionCount r := by
  induction r with
  | zero => omega
  | succ r ih =>
    rw [freeInvolutionCount_succ]
    rcases r with _ | r
    · simp [freeInvolutionCount]
    · exact Nat.mul_pos (by omega) (ih (by omega))

/-- The free involution count is strictly increasing for r ≥ 1.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_strict_mono (r : Nat) (hr : 1 ≤ r) :
    freeInvolutionCount r < freeInvolutionCount (r + 1) := by
  rw [freeInvolutionCount_succ]
  have hpos := freeInvolutionCount_pos r hr
  -- fIC(r+1) = (2r+1) * fIC(r) ≥ 3 * fIC(r) > fIC(r) since 2r+1 ≥ 3 for r ≥ 1
  calc freeInvolutionCount r
      < 2 * freeInvolutionCount r := by omega
    _ ≤ (2 * r + 1) * freeInvolutionCount r := by
        apply Nat.mul_le_mul_right; omega

/-- Fiberwise free involution counts multiply across independent fibers.
    thm:fiberwise-free-involution-matching-entropy -/
theorem fiberwiseFreeInvolutionCount_total_eq_prod_doubleFactorial
    {B : Type*} [Fintype B] (r : B → Nat) :
    (∏ b, freeInvolutionCount (r b)) =
      ∏ b, Nat.doubleFactorial (2 * r b - 1) := by
  simpa using
    Finset.prod_congr rfl (fun b _ => freeInvolutionCount_eq_doubleFactorial (r b))

/-- Fiberwise total free involution count satisfies the factorial product formula.
    thm:fiberwise-free-involution-matching-entropy -/
theorem fiberwiseFreeInvolutionCount_total_formula
    {B : Type*} [Fintype B] (r : B → Nat) :
    (∏ b, freeInvolutionCount (r b)) * (∏ b, (2 ^ (r b) * (r b).factorial)) =
      ∏ b, (2 * r b).factorial := by
  calc
    (∏ b, freeInvolutionCount (r b)) * (∏ b, (2 ^ (r b) * (r b).factorial))
        = ∏ b, (freeInvolutionCount (r b) * (2 ^ (r b) * (r b).factorial)) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ b, (2 * r b).factorial := by
          refine Finset.prod_congr rfl ?_
          intro b hb
          simpa using freeInvolutionCount_formula (r b)

-- ══════════════════════════════════════════════════════════════
-- Phase R253: Free involution existence on even sets
-- ══════════════════════════════════════════════════════════════

/-- A free involution exists on Fin(2k) for k ≥ 1: swap adjacent pairs (0,1), (2,3), ...
    f(2i) = 2i+1, f(2i+1) = 2i.
    thm:fiberwise-free-involution-matching-entropy -/
theorem free_involution_exists_even (k : Nat) (_hk : 1 ≤ k) :
    ∃ f : Fin (2 * k) → Fin (2 * k),
      Function.Bijective f ∧ (∀ x, f (f x) = x) ∧ (∀ x, f x ≠ x) := by
  -- Use the permutation that swaps i with i+1 when i is even, and i with i-1 when i is odd
  -- Equivalently: flip the last bit of i
  have hswap : ∀ i : Fin (2 * k), (if i.val % 2 = 0 then i.val + 1 else i.val - 1) < 2 * k := by
    intro i
    have hi := i.isLt
    split
    · -- even: i+1 < 2k because i is even and i < 2k means i ≤ 2k-2
      omega
    · -- odd: i-1 < 2k trivially since i-1 < i < 2k
      omega
  let f : Fin (2 * k) → Fin (2 * k) :=
    fun i => ⟨if i.val % 2 = 0 then i.val + 1 else i.val - 1, hswap i⟩
  have hinv : ∀ x : Fin (2 * k), (f (f x)).val = x.val := by
    intro x; simp only [f]
    have hx := x.isLt
    split <;> split <;> omega
  have hfp : ∀ x : Fin (2 * k), (f x).val ≠ x.val := by
    intro x; simp only [f]; split <;> omega
  refine ⟨f, ⟨?_, ?_⟩, fun x => Fin.ext (hinv x), fun x hx => hfp x (congrArg Fin.val hx)⟩
  · intro a b hab
    have : (f (f a)).val = (f (f b)).val := by rw [hab]
    rw [hinv a, hinv b] at this; exact Fin.ext this
  · exact fun b => ⟨f b, Fin.ext (hinv b)⟩

/-- Free involution count values and formula.
    thm:fiberwise-free-involution-matching-entropy -/
theorem paper_freeInvolutionCount_values_and_formula :
    freeInvolutionCount 1 = 1 ∧
    freeInvolutionCount 2 = 3 ∧
    freeInvolutionCount 3 = 15 ∧
    freeInvolutionCount 4 = 105 ∧
    (∀ r : Nat, freeInvolutionCount r * (2 ^ r * r.factorial) = (2 * r).factorial) ∧
    (∀ k : Nat, ¬ ∃ f : Fin (2*k+1) → Fin (2*k+1),
      Function.Bijective f ∧ (∀ x, f (f x) = x) ∧ (∀ x, f x ≠ x)) := by
  exact ⟨freeInvolutionCount_small.1, freeInvolutionCount_small.2.1,
    freeInvolutionCount_small.2.2, by native_decide,
    freeInvolutionCount_formula, no_free_involution_on_odd⟩

/-- Free involution count is at least r! for r >= 1.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_ge_factorial : ∀ r : Nat, 1 ≤ r →
    r.factorial ≤ freeInvolutionCount r
  | 1, _ => by simp [freeInvolutionCount, Nat.factorial]
  | r + 2, _ => by
    have ih := freeInvolutionCount_ge_factorial (r + 1) (by omega)
    rw [freeInvolutionCount_succ]
    calc (r + 2).factorial = (r + 2) * (r + 1).factorial := Nat.factorial_succ (r + 1)
      _ ≤ (2 * (r + 1) + 1) * freeInvolutionCount (r + 1) :=
        Nat.mul_le_mul (by omega) ih

/-- The free involution count (2r-1)!! is always odd.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_odd : ∀ r : Nat, ¬ 2 ∣ freeInvolutionCount r
  | 0 => by simp [freeInvolutionCount]
  | r + 1 => by
    rw [freeInvolutionCount_succ]
    intro h
    have ih := freeInvolutionCount_odd r
    -- (2r+1) is odd, and freeInvolutionCount r is odd by IH
    -- so their product is odd
    have hodd : ¬ 2 ∣ (2 * r + 1) := by omega
    exact ih (or_iff_not_imp_left.mp ((Nat.Prime.dvd_mul Nat.prime_two).mp h) hodd)

-- ══════════════════════════════════════════════════════════════
-- Phase R297: Divisibility, factorial bound, package
-- ══════════════════════════════════════════════════════════════

/-- 3 divides freeInvolutionCount r for r ≥ 2.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_three : ∀ r : Nat, 2 ≤ r →
    3 ∣ freeInvolutionCount r
  | 2, _ => ⟨1, by rw [freeInvolutionCount_small.2.1]⟩
  | r + 3, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_three (r + 2) (by omega)) _

/-- 15 divides freeInvolutionCount r for r ≥ 3.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_fifteen : ∀ r : Nat, 3 ≤ r →
    15 ∣ freeInvolutionCount r
  | 3, _ => ⟨1, by rw [freeInvolutionCount_small.2.2]⟩
  | r + 4, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_fifteen (r + 3) (by omega)) _

/-- f(r) · 2^r ≤ (2r)! (from f(r) · 2^r · r! = (2r)!).
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_le_factorial_div (r : Nat) :
    freeInvolutionCount r * 2 ^ r ≤ (2 * r).factorial := by
  have h := freeInvolutionCount_formula r
  calc freeInvolutionCount r * 2 ^ r
      ≤ freeInvolutionCount r * 2 ^ r * r.factorial :=
        Nat.le_mul_of_pos_right _ (Nat.factorial_pos r)
    _ = freeInvolutionCount r * (2 ^ r * r.factorial) := by ring
    _ = (2 * r).factorial := h

/-- Involution count divisibility and recurrence package.
    thm:fiberwise-free-involution-matching-entropy -/
theorem paper_gu_involution_divisibility_package :
    freeInvolutionCount 2 = 3 ∧ freeInvolutionCount 3 = 15 ∧
    freeInvolutionCount 4 = 105 ∧ freeInvolutionCount 5 = 945 ∧
    3 ∣ freeInvolutionCount 2 ∧ 15 ∣ freeInvolutionCount 3 ∧
    105 ∣ freeInvolutionCount 4 ∧
    freeInvolutionCount 3 = 5 * freeInvolutionCount 2 ∧
    freeInvolutionCount 4 = 7 * freeInvolutionCount 3 ∧
    freeInvolutionCount 5 = 9 * freeInvolutionCount 4 := by
  have h1 := freeInvolutionCount_small.2.1  -- f(2) = 3
  have h2 := freeInvolutionCount_small.2.2  -- f(3) = 15
  refine ⟨h1, h2, by native_decide, by native_decide,
    ⟨1, by rw [h1]⟩, ⟨1, by rw [h2]⟩, ⟨1, by native_decide⟩, ?_, ?_, ?_⟩
  · rw [h2, h1]
  · rw [freeInvolutionCount_succ, h2]
  · rw [freeInvolutionCount_succ, freeInvolutionCount_succ, h2]

-- ══════════════════════════════════════════════════════════════
-- Phase R302: Free involution count log-convexity
-- ══════════════════════════════════════════════════════════════

/-- Free involution count ratio is strictly increasing.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_ratio (r : Nat) :
    freeInvolutionCount (r + 1) = (2 * r + 1) * freeInvolutionCount r :=
  freeInvolutionCount_succ r

/-- The ratio 2r+1 is strictly increasing.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_ratio_increasing (r : Nat) :
    (2 * r + 1) < (2 * (r + 1) + 1) := by omega

/-- Log-convexity: f(r+2)·f(r) ≥ f(r+1)².
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_log_convex (r : Nat) :
    freeInvolutionCount (r + 2) * freeInvolutionCount r ≥
    freeInvolutionCount (r + 1) ^ 2 := by
  rw [freeInvolutionCount_succ (r + 1), freeInvolutionCount_succ r, sq]
  nlinarith [Nat.zero_le (freeInvolutionCount r)]

/-- Strict log-convexity for r ≥ 1.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_strict_log_convex (r : Nat) (hr : 1 ≤ r) :
    freeInvolutionCount (r + 2) * freeInvolutionCount r >
    freeInvolutionCount (r + 1) ^ 2 := by
  rw [freeInvolutionCount_succ (r + 1), freeInvolutionCount_succ r, sq]
  have hpos := freeInvolutionCount_pos r hr
  set f := freeInvolutionCount r with hf_def
  -- Goal: (2*(r+1)+1) * ((2*r+1)*f) * f > (2*r+1)*f * ((2*r+1)*f)
  -- = (2r+3)*(2r+1)*f^2 > (2r+1)^2*f^2
  nlinarith [sq_nonneg f, mul_pos (show 0 < 2 * r + 1 by omega) hpos]

/-- Paper package: log-convexity + concrete values.
    thm:fiberwise-free-involution-matching-entropy -/
theorem paper_freeInvolutionCount_log_convexity_package :
    (∀ r, freeInvolutionCount (r + 1) = (2 * r + 1) * freeInvolutionCount r) ∧
    (∀ r, freeInvolutionCount (r + 2) * freeInvolutionCount r ≥
      freeInvolutionCount (r + 1) ^ 2) ∧
    freeInvolutionCount 6 = 10395 ∧
    freeInvolutionCount 7 = 135135 := by
  refine ⟨freeInvolutionCount_succ, freeInvolutionCount_log_convex, ?_, ?_⟩
  · rw [freeInvolutionCount_succ]; norm_num [freeInvolutionCount_succ, freeInvolutionCount]
  · rw [freeInvolutionCount_succ]; norm_num [freeInvolutionCount_succ, freeInvolutionCount]

-- ══════════════════════════════════════════════════════════════
-- Phase R309: freeInvolutionCount divisibility
-- ══════════════════════════════════════════════════════════════

/-- thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_seven : ∀ r : Nat, 4 ≤ r →
    7 ∣ freeInvolutionCount r
  | 4, _ => ⟨15, by native_decide⟩
  | r + 5, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_seven (r + 4) (by omega)) _

/-- thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_105 : ∀ r : Nat, 4 ≤ r →
    105 ∣ freeInvolutionCount r
  | 4, _ => ⟨1, by native_decide⟩
  | r + 5, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_105 (r + 4) (by omega)) _

/-- Paper package. thm:fiberwise-free-involution-matching-entropy -/
theorem paper_freeInvolutionCount_dvd_extended :
    (∀ r, 4 ≤ r → 7 ∣ freeInvolutionCount r) ∧
    (∀ r, 4 ≤ r → 105 ∣ freeInvolutionCount r) ∧
    freeInvolutionCount 4 = 105 ∧
    freeInvolutionCount 4 / 105 = 1 := by
  exact ⟨freeInvolutionCount_dvd_seven, freeInvolutionCount_dvd_105,
    by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R312: freeInvolutionCount dvd 9 + dvd 945
-- ══════════════════════════════════════════════════════════════

/-- thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_nine : ∀ r : Nat, 5 ≤ r →
    9 ∣ freeInvolutionCount r
  | 5, _ => ⟨105, by native_decide⟩
  | r + 6, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_nine (r + 5) (by omega)) _

/-- thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_dvd_945 : ∀ r : Nat, 5 ≤ r →
    945 ∣ freeInvolutionCount r
  | 5, _ => ⟨1, by native_decide⟩
  | r + 6, _ => by
    rw [freeInvolutionCount_succ]
    exact Dvd.dvd.mul_left (freeInvolutionCount_dvd_945 (r + 5) (by omega)) _

/-- Paper package. thm:fiberwise-free-involution-matching-entropy -/
theorem paper_freeInvolutionCount_dvd_hierarchy :
    (∀ r, 2 ≤ r → 3 ∣ freeInvolutionCount r) ∧
    (∀ r, 3 ≤ r → 15 ∣ freeInvolutionCount r) ∧
    (∀ r, 4 ≤ r → 105 ∣ freeInvolutionCount r) ∧
    (∀ r, 5 ≤ r → 945 ∣ freeInvolutionCount r) := by
  exact ⟨freeInvolutionCount_dvd_three, freeInvolutionCount_dvd_fifteen,
    freeInvolutionCount_dvd_105, freeInvolutionCount_dvd_945⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R334: Free involution count concrete values
-- ══════════════════════════════════════════════════════════════

/-- f(4) = 7!! = 105.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_four : freeInvolutionCount 4 = 105 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_small.2.2]

/-- f(5) = 9!! = 945.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_five : freeInvolutionCount 5 = 945 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_four]

/-- f(6) = 11!! = 10395.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_six : freeInvolutionCount 6 = 10395 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_five]

/-- f(7) = 13!! = 135135.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_seven : freeInvolutionCount 7 = 135135 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_six]

/-- f(8) = 15!! = 2027025.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_eight : freeInvolutionCount 8 = 2027025 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_seven]

/-- f(9) = 17!! = 34459425.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_nine : freeInvolutionCount 9 = 34459425 := by
  rw [freeInvolutionCount_succ, freeInvolutionCount_eight]

/-- Log-convexity: f(r)² ≤ f(r-1) · f(r+1) for r ≥ 1.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_sq_le_mul (r : Nat) (hr : 1 ≤ r) :
    freeInvolutionCount r ^ 2 ≤
    freeInvolutionCount (r - 1) * freeInvolutionCount (r + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [show k + 1 - 1 = k from by omega]
  -- f(k+1) = (2k+1)*f(k), f(k+2) = (2k+3)*f(k+1)
  have h1 := freeInvolutionCount_succ k
  have h2 := freeInvolutionCount_succ (k + 1)
  -- f(k+1)^2 = (2k+1)^2 * f(k)^2
  -- f(k) * f(k+2) = f(k) * (2k+3) * f(k+1) = (2k+3)*(2k+1)*f(k)^2
  rw [h1, h2, sq]
  -- (2k+1)*f(k) * ((2k+1)*f(k)) ≤ f(k) * ((2*(k+1)+1) * ((2k+1)*f(k)))
  nlinarith [freeInvolutionCount_pos (k + 1) (by omega)]

/-- Exponential lower bound: (2r-1)!! ≥ 2^(r-1).
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_ge_two_pow : ∀ r : Nat, 1 ≤ r →
    2 ^ (r - 1) ≤ freeInvolutionCount r
  | 1, _ => by simp [freeInvolutionCount]
  | r + 2, _ => by
    have ih := freeInvolutionCount_ge_two_pow (r + 1) (by omega)
    rw [freeInvolutionCount_succ, show r + 2 - 1 = r + 1 from by omega]
    calc 2 ^ (r + 1) = 2 * 2 ^ r := by ring
      _ = 2 * 2 ^ (r + 1 - 1) := by rw [show r + 1 - 1 = r from by omega]
      _ ≤ 2 * freeInvolutionCount (r + 1) := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * (r + 1) + 1) * freeInvolutionCount (r + 1) :=
          Nat.mul_le_mul_right _ (by omega)

/-- Per-fiber information cost is at least (r-1) bits.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_log_lower (r : Nat) (hr : 1 ≤ r) :
    r - 1 ≤ Nat.log 2 (freeInvolutionCount r) := by
  have h1 := freeInvolutionCount_ge_two_pow r hr
  calc r - 1 = Nat.log 2 (2 ^ (r - 1)) := (Nat.log_pow (by omega) (r - 1)).symm
    _ ≤ Nat.log 2 (freeInvolutionCount r) := Nat.log_mono_right h1

/-- Upper bound: (2r-1)!! ≤ (2r)^r.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_le_two_r_pow : ∀ r : Nat,
    freeInvolutionCount r ≤ (2 * r) ^ r
  | 0 => by simp [freeInvolutionCount]
  | r + 1 => by
    rw [freeInvolutionCount_succ]
    calc (2 * r + 1) * freeInvolutionCount r
        ≤ (2 * r + 1) * (2 * r) ^ r :=
          Nat.mul_le_mul_left _ (freeInvolutionCount_le_two_r_pow r)
      _ ≤ (2 * (r + 1)) * (2 * (r + 1)) ^ r :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) r)
      _ = (2 * (r + 1)) ^ (r + 1) := by rw [pow_succ]; ring

/-- Paper-facing package of the free involution information bounds.
    thm:fiberwise-free-involution-matching-entropy -/
theorem paper_freeInvolutionCount_information_bounds :
    (∀ r : ℕ, 1 ≤ r → r - 1 ≤ Nat.log 2 (freeInvolutionCount r)) ∧
    (∀ r : ℕ, freeInvolutionCount r ≤ (2 * r) ^ r) := by
  exact ⟨freeInvolutionCount_log_lower, freeInvolutionCount_le_two_r_pow⟩

end Omega.GU
