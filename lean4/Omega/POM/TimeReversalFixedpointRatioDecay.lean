import Mathlib.Tactic
import Omega.Folding.ShiftDynamics
import Omega.POM.ToggleOrder
import Omega.Zeta.LucasBarrier

namespace Omega.POM

open Omega.POM.ToggleOrder

private theorem timeReversalFix_even (n : Nat) :
    timeReversalFix (2 * n) = Nat.fib (n + 1) := by
  have hEven : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  simp [timeReversalFix, hEven, hdiv]

private theorem lucasBarrier_eq_lucasNum (n : Nat) :
    Omega.Zeta.LucasBarrier.lucas (n + 1) = Omega.lucasNum (n + 1) := by
  rw [Omega.lucasNum_eq_fib (n + 1) (by omega)]
  simp [Omega.Zeta.LucasBarrier.lucas, add_comm, add_left_comm]

private theorem fiberTimeReversalVertexCount_pos : ∀ lengths : List Nat,
    0 < fiberTimeReversalVertexCount lengths
  | [] => by
      simp [fiberTimeReversalVertexCount]
  | ℓ :: lengths => by
      have hfib : 0 < Nat.fib (ℓ + 2) := Nat.fib_pos.mpr (by omega)
      simpa [fiberTimeReversalVertexCount] using
        Nat.mul_pos hfib (fiberTimeReversalVertexCount_pos lengths)

private theorem fiber_ratio_formula (lengths : List Nat) :
    ((fiberTimeReversalFixCount lengths : ℚ) / (fiberTimeReversalVertexCount lengths : ℚ)) =
      (lengths.map (fun ℓ => (timeReversalFix ℓ : ℚ) / (Nat.fib (ℓ + 2) : ℚ))).prod := by
  induction lengths with
  | nil =>
      simp [fiberTimeReversalFixCount, fiberTimeReversalVertexCount]
  | cons ℓ lengths ih =>
      have hfib : (Nat.fib (ℓ + 2) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))
      have hrest : (fiberTimeReversalVertexCount lengths : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (fiberTimeReversalVertexCount_pos lengths)
      rw [fiberTimeReversalFixCount, fiberTimeReversalVertexCount, List.map_cons, List.prod_cons,
        Nat.cast_mul, Nat.cast_mul]
      calc
        ((timeReversalFix ℓ : ℚ) * (fiberTimeReversalFixCount lengths : ℚ)) /
            ((Nat.fib (ℓ + 2) : ℚ) * (fiberTimeReversalVertexCount lengths : ℚ)) =
            ((timeReversalFix ℓ : ℚ) / (Nat.fib (ℓ + 2) : ℚ)) *
              ((fiberTimeReversalFixCount lengths : ℚ) /
                (fiberTimeReversalVertexCount lengths : ℚ)) := by
              field_simp [hfib, hrest]
        _ = ((timeReversalFix ℓ : ℚ) / (Nat.fib (ℓ + 2) : ℚ)) *
              (List.map (fun ℓ => (timeReversalFix ℓ : ℚ) / (Nat.fib (ℓ + 2) : ℚ)) lengths).prod := by
              rw [ih]

/-- Paper-facing fixed-point ratio package: the fiberwise ratio factors over path components, and
for even paths the ratio collapses to the reciprocal Lucas number. -/
theorem paper_pom_time_reversal_fixedpoint_ratio_decay (lengths : List Nat) :
    (((fiberTimeReversalFixCount lengths : ℚ) / (fiberTimeReversalVertexCount lengths : ℚ)) =
      (lengths.map (fun ℓ => (timeReversalFix ℓ : ℚ) / (Nat.fib (ℓ + 2) : ℚ))).prod) ∧
      (∀ n : Nat, ((timeReversalFix (2 * n) : ℚ) / (Nat.fib (2 * n + 2) : ℚ)) =
        1 / (Omega.Zeta.LucasBarrier.lucas (n + 1) : ℚ)) := by
  constructor
  · exact fiber_ratio_formula lengths
  · intro n
    have hfix : timeReversalFix (2 * n) = Nat.fib (n + 1) := timeReversalFix_even n
    have htwo : 2 * n + 2 = 2 * (n + 1) := by omega
    have hdouble : Nat.fib (2 * n + 2) = Nat.fib (n + 1) * Omega.lucasNum (n + 1) := by
      simpa [htwo] using (Omega.fib_double_eq_mul_lucas (n + 1))
    have hlucas : Omega.Zeta.LucasBarrier.lucas (n + 1) = Omega.lucasNum (n + 1) :=
      lucasBarrier_eq_lucasNum n
    have hcast :
        (Nat.fib (2 * n + 2) : ℚ) =
          (Nat.fib (n + 1) : ℚ) * (Omega.Zeta.LucasBarrier.lucas (n + 1) : ℚ) := by
      rw [hdouble, hlucas, Nat.cast_mul]
    have hfib : (Nat.fib (n + 1) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))
    have hlucasq : (Omega.Zeta.LucasBarrier.lucas (n + 1) : ℚ) ≠ 0 := by
      have hpos : 0 < Omega.Zeta.LucasBarrier.lucas (n + 1) := by
        unfold Omega.Zeta.LucasBarrier.lucas
        exact Nat.add_pos_right _ (Nat.fib_pos.mpr (by omega))
      exact_mod_cast Nat.ne_of_gt hpos
    rw [hfix, hcast, div_eq_mul_inv, one_div]
    simp [mul_assoc, mul_left_comm, mul_comm, hfib, hlucasq]

end Omega.POM
