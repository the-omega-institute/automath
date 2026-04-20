import Mathlib

namespace Omega.CircleDimension

open Finset
open scoped BigOperators

/-- A concrete hyperplane-arrangement upper bound for the number of length-`t` cylinder regions
cut out by at most `r * t` affine walls in dimension `d`. -/
def polyhedralGateWordComplexity (r d t : Nat) : Nat :=
  Finset.sum (range (d + 1)) fun k => (r * t) ^ k

lemma polyhedralGateWordComplexity_le_polynomial (r d t : Nat) (ht : 1 ≤ t) :
    polyhedralGateWordComplexity r d t ≤
      Finset.sum (range (d + 1)) (fun k => r ^ k) * t ^ d := by
  unfold polyhedralGateWordComplexity
  calc
    Finset.sum (range (d + 1)) (fun k => (r * t) ^ k) =
        Finset.sum (range (d + 1)) (fun k => r ^ k * t ^ k) := by
      refine sum_congr rfl ?_
      intro k hk
      rw [Nat.mul_pow]
    _ ≤ Finset.sum (range (d + 1)) (fun k => r ^ k * t ^ d) := by
      refine sum_le_sum ?_
      intro k hk
      refine Nat.mul_le_mul_left (r ^ k) ?_
      exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt ht) (Nat.lt_succ_iff.mp (mem_range.mp hk))
    _ = Finset.sum (range (d + 1)) (fun k => r ^ k) * t ^ d := by
      rw [sum_mul]

/-- Paper-facing polynomial upper bound for the concrete polyhedral-gate cylinder model.
    thm:cdim-polyhedral-gate-word-complexity-td -/
theorem paper_cdim_polyhedral_gate_word_complexity_td (r d : Nat) :
    ∃ C : Nat, ∀ t, t ≥ 1 → polyhedralGateWordComplexity r d t ≤ C * t ^ d := by
  refine ⟨Finset.sum (range (d + 1)) (fun k => r ^ k), ?_⟩
  intro t ht
  exact polyhedralGateWordComplexity_le_polynomial r d t ht

end Omega.CircleDimension
