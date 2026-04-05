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

end Omega.GU
