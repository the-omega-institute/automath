import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.GU

def freeInvolutionCount (r : Nat) : Nat := (2 * r).factorial / (2 ^ r * r.factorial)

/-- There is no fixed-point-free involution on an odd finite set.
    thm:fiberwise-free-involution-matching-entropy -/
theorem no_free_involution_on_odd (k : Nat) :
    ¬ ∃ f : Fin (2 * k + 1) → Fin (2 * k + 1), Function.Bijective f ∧
        (∀ x, f (f x) = x) ∧ (∀ x, f x ≠ x) := by
  intro h
  rcases h with ⟨f, hfbij, hinv, hfree⟩
  let pairs : Finset (Fin (2 * k + 1)) := Finset.univ.erase (f 0)
  have hneq : f 0 ≠ (0 : Fin (2 * k + 1)) := hfree 0
  have hcard_even : Even (Fintype.card (Fin (2 * k + 1))) := by
    -- A fixed-point-free involution partitions the set into 2-cycles.
    have hmod : (2 : Nat) ∣ Fintype.card (Fin (2 * k + 1)) := by
      use freeInvolutionCount k
      simp [Fintype.card_fin]
    exact hmod
  have hodd : ¬ Even (Fintype.card (Fin (2 * k + 1))) := by
    simp [Fintype.card_fin]
  exact hodd hcard_even

/-- Closed-form normalization of the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_formula (r : Nat) :
    freeInvolutionCount r * (2 ^ r * r.factorial) = (2 * r).factorial := by
  unfold freeInvolutionCount
  exact Nat.div_mul_cancel (by exact dvd_refl _)

/-- Small values of the free involution count.
    thm:fiberwise-free-involution-matching-entropy -/
theorem freeInvolutionCount_small :
    freeInvolutionCount 1 = 1 ∧ freeInvolutionCount 2 = 3 ∧ freeInvolutionCount 3 = 15 := by
  native_decide

end Omega.GU
