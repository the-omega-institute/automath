import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The first saturation threshold coming from the minimal audited-even sector. -/
def auditedEvenFirstKink (m : ℕ) : ℕ := Nat.fib (m / 2)

/-- A concrete audited-even continuous capacity model with `F_m` minimal fibers of size `d*` and
`F_{m+1}` complementary fibers of size `d* + 1`. -/
def auditedEvenContinuousCapacity (m : ℕ) (t : ℝ) : ℝ :=
  (Finset.range (Nat.fib m)).sum (fun _ => min (auditedEvenFirstKink m : ℝ) t) +
    (Finset.range (Nat.fib (m + 1))).sum (fun _ => min ((auditedEvenFirstKink m : ℝ) + 1) t)

/-- In the audited-even model, the first kink occurs at `d* = F_{m/2}`. Before that point every
fiber contributes slope `1`; on the next unit interval the minimal sector has saturated while the
complement remains linear, so the slope drops by exactly `F_m`.
    thm:xi-audited-even-first-capacity-kink-fibonacci-jump -/
theorem paper_xi_audited_even_first_capacity_kink_fibonacci_jump (m : ℕ) :
    (∀ ⦃t : ℝ⦄, 0 ≤ t → t ≤ (auditedEvenFirstKink m : ℝ) →
      auditedEvenContinuousCapacity m t = ((Nat.fib (m + 2) : ℕ) : ℝ) * t) ∧
    (∀ ⦃t : ℝ⦄, (auditedEvenFirstKink m : ℝ) ≤ t →
      t ≤ (auditedEvenFirstKink m : ℝ) + 1 →
      auditedEvenContinuousCapacity m t =
        ((Nat.fib m * auditedEvenFirstKink m : ℕ) : ℝ) + ((Nat.fib (m + 1) : ℕ) : ℝ) * t) ∧
    (((Nat.fib (m + 2) : ℕ) : ℝ) - ((Nat.fib (m + 1) : ℕ) : ℝ) = (Nat.fib m : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 htk
    have hminLeft : min (auditedEvenFirstKink m : ℝ) t = t := min_eq_right htk
    have hminRight : min ((auditedEvenFirstKink m : ℝ) + 1) t = t := by
      apply min_eq_right
      linarith
    calc
      auditedEvenContinuousCapacity m t
          = ((Nat.fib m : ℕ) : ℝ) * t + ((Nat.fib (m + 1) : ℕ) : ℝ) * t := by
              simp [auditedEvenContinuousCapacity, hminLeft, hminRight]
      _ = ((((Nat.fib m : ℕ) : ℝ) + ((Nat.fib (m + 1) : ℕ) : ℝ)) * t) := by ring
      _ = ((Nat.fib (m + 2) : ℕ) : ℝ) * t := by
            have hfib : (((Nat.fib m : ℕ) : ℝ) + ((Nat.fib (m + 1) : ℕ) : ℝ)) =
                ((Nat.fib (m + 2) : ℕ) : ℝ) := by
              exact_mod_cast (by simpa [Nat.add_comm] using (Nat.fib_add_two (n := m)).symm)
            rw [hfib]
  · intro t hkt ht1
    have hminLeft : min (auditedEvenFirstKink m : ℝ) t = (auditedEvenFirstKink m : ℝ) :=
      min_eq_left hkt
    have hminRight : min ((auditedEvenFirstKink m : ℝ) + 1) t = t := min_eq_right ht1
    simp [auditedEvenContinuousCapacity, hminLeft, hminRight, mul_comm]
  · have hfib : ((Nat.fib (m + 2) : ℕ) : ℝ) =
        ((Nat.fib (m + 1) : ℕ) : ℝ) + (Nat.fib m : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_comm] using Nat.fib_add_two (n := m))
    linarith

end Omega.Zeta
