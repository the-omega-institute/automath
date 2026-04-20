import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Averaging the single-fiber defect bound `q / (4 d(x))` against the exact fiber weights
`d(x) / ∑_y d(y)` collapses to the global bound `(q * |X|) / (4 * ∑_y d(y))`.
    thm:xi-godel-fiber-index-mod-uniformity-independence -/
theorem paper_xi_godel_fiber_index_mod_uniformity_independence {X : Type*} [Fintype X]
    (d : X → ℕ) (q : ℕ) (hd : ∀ x, 0 < d x) :
    (∑ x, ((d x : ℝ) / (∑ y, (d y : ℝ))) * ((q : ℝ) / (4 * (d x : ℝ)))) =
      ((q : ℝ) * Fintype.card X) / (4 * ∑ y, (d y : ℝ)) := by
  classical
  by_cases hX : IsEmpty X
  · letI := hX
    simp
  · letI := not_isEmpty_iff.mp hX
    let S : ℝ := ∑ y, (d y : ℝ)
    have hS_pos : 0 < S := by
      obtain ⟨x⟩ := ‹Nonempty X›
      have hx_pos : 0 < (d x : ℝ) := by exact_mod_cast hd x
      have hx_le : (d x : ℝ) ≤ S := by
        have hx_le_nat : d x ≤ ∑ y, d y := by
          exact Finset.single_le_sum (fun y _ => Nat.zero_le (d y)) (Finset.mem_univ x)
        dsimp [S]
        exact_mod_cast hx_le_nat
      exact lt_of_lt_of_le hx_pos hx_le
    have hterm :
        ∀ x : X, ((d x : ℝ) / S) * ((q : ℝ) / (4 * (d x : ℝ))) = (q : ℝ) / (4 * S) := by
      intro x
      have hdx : (d x : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (hd x))
      field_simp [S, hS_pos.ne', hdx]
    calc
      (∑ x, ((d x : ℝ) / S) * ((q : ℝ) / (4 * (d x : ℝ)))) =
          ∑ x, (q : ℝ) / (4 * S) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact hterm x
      _ = ((q : ℝ) * Fintype.card X) / (4 * S) := by
        simp [S, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
      _ = ((q : ℝ) * Fintype.card X) / (4 * ∑ y, (d y : ℝ)) := by
        simp [S]
