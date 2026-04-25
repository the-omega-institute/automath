import Mathlib.Tactic
import Omega.Core.Fib
import Omega.POM.ToggleOrder

namespace Omega.POM

open Omega.POM.ToggleOrder

private lemma pom_time_reversal_orbit_count_component_parity (ℓ : ℕ) :
    Nat.fib (ℓ + 2) % 2 = timeReversalFix ℓ % 2 := by
  by_cases hEven : ℓ % 2 = 0
  · rw [timeReversalFix, if_pos hEven, Omega.fib_mod_two_period (ℓ + 2),
      Omega.fib_mod_two_period (ℓ / 2 + 1)]
    have hk : (ℓ / 2) % 3 = 0 ∨ (ℓ / 2) % 3 = 1 ∨ (ℓ / 2) % 3 = 2 := by
      omega
    rcases hk with hk | hk | hk
    · have h1 : (ℓ + 2) % 3 = 2 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 1 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 1 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 2 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 0 := by omega
      have h2 : (ℓ / 2 + 1) % 3 = 0 := by omega
      simp [h1, h2]
  · rw [timeReversalFix, if_neg hEven, Omega.fib_mod_two_period (ℓ + 2),
      Omega.fib_mod_two_period (ℓ / 2 + 3)]
    have hk : (ℓ / 2) % 3 = 0 ∨ (ℓ / 2) % 3 = 1 ∨ (ℓ / 2) % 3 = 2 := by
      omega
    rcases hk with hk | hk | hk
    · have h1 : (ℓ + 2) % 3 = 0 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 0 := by omega
      simp [h1, h2]
    · have h1 : (ℓ + 2) % 3 = 2 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 1 := by omega
      rw [h1, h2]
      native_decide
    · have h1 : (ℓ + 2) % 3 = 1 := by omega
      have h2 : (ℓ / 2 + 3) % 3 = 2 := by omega
      rw [h1, h2]
      native_decide

private lemma pom_time_reversal_orbit_count_fix_le_vertex : ∀ lengths : List Nat,
    fiberTimeReversalFixCount lengths ≤ fiberTimeReversalVertexCount lengths
  | [] => by
      simp [fiberTimeReversalFixCount, fiberTimeReversalVertexCount]
  | ℓ :: lengths => by
      have hhead : timeReversalFix ℓ ≤ Nat.fib (ℓ + 2) := by
        cases ℓ with
        | zero =>
            native_decide
        | succ n =>
            exact timeReversalFix_le_total (Nat.succ n) (Nat.succ_le_succ (Nat.zero_le n))
      have htail := pom_time_reversal_orbit_count_fix_le_vertex lengths
      simpa [fiberTimeReversalFixCount, fiberTimeReversalVertexCount] using
        Nat.mul_le_mul hhead htail

private lemma pom_time_reversal_orbit_count_parity : ∀ lengths : List Nat,
    fiberTimeReversalVertexCount lengths % 2 = fiberTimeReversalFixCount lengths % 2
  | [] => by
      simp [fiberTimeReversalVertexCount, fiberTimeReversalFixCount]
  | ℓ :: lengths => by
      calc
        fiberTimeReversalVertexCount (ℓ :: lengths) % 2 =
            (Nat.fib (ℓ + 2) % 2) * (fiberTimeReversalVertexCount lengths % 2) % 2 := by
              simp [fiberTimeReversalVertexCount, Nat.mul_mod]
        _ = (timeReversalFix ℓ % 2) * (fiberTimeReversalFixCount lengths % 2) % 2 := by
              rw [pom_time_reversal_orbit_count_component_parity,
                pom_time_reversal_orbit_count_parity]
        _ = fiberTimeReversalFixCount (ℓ :: lengths) % 2 := by
              simp [fiberTimeReversalFixCount, Nat.mul_mod]

/-- Paper label: `cor:pom-time-reversal-orbit-count`. The orbit count of the fiberwise
time-reversal involution is the fixed-point count plus the transposition count, equivalently the
half-sum of the total state count and the fixed-point count. -/
theorem paper_pom_time_reversal_orbit_count (lengths : List Nat) :
    fiberTimeReversalFixCount lengths + fiberTimeReversalSignExp lengths =
      (fiberTimeReversalVertexCount lengths + fiberTimeReversalFixCount lengths) / 2 := by
  unfold fiberTimeReversalSignExp
  have hle := pom_time_reversal_orbit_count_fix_le_vertex lengths
  have hpar := pom_time_reversal_orbit_count_parity lengths
  omega

end Omega.POM
