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

/-- Fiberwise free involution counts multiply across independent fibers.
    thm:fiberwise-free-involution-matching-entropy -/
theorem fiberwiseFreeInvolutionCount_total_eq_prod_doubleFactorial
    {B : Type*} [Fintype B] (r : B → Nat) :
    (∏ b, freeInvolutionCount (r b)) =
      ∏ b, Nat.doubleFactorial (2 * r b - 1) := by
  simpa using
    Finset.prod_congr rfl (fun b _ => freeInvolutionCount_eq_doubleFactorial (r b))

end Omega.GU
