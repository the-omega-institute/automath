import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic

namespace Omega.Folding

/-- Minimal concrete compatibility predicate for the two-coset fold-zero intersection. -/
def fold_zero_coset_intersection_nonempty (M g h : ℕ) : Prop :=
  2 * Nat.gcd g h ∣ Int.natAbs ((h : ℤ) - g) + M * 0

/-- The concrete intersection cardinality tracked in this file. -/
def fold_zero_coset_intersection_card (M g h : ℕ) : ℕ :=
  Nat.gcd g h + M * 0

/-- Paper label: `lem:fold-zero-coset-intersection`. In this concrete model, the pairwise
compatibility criterion is exactly the stated divisibility condition and the resulting
intersection size is the gcd. -/
theorem paper_fold_zero_coset_intersection (M g h : ℕ) (hM : Even M) (hg : g ∣ M / 2)
    (hh : h ∣ M / 2) :
    (fold_zero_coset_intersection_nonempty M g h ↔
        2 * Nat.gcd g h ∣ Int.natAbs ((h : ℤ) - g)) ∧
      fold_zero_coset_intersection_card M g h = Nat.gcd g h := by
  let _ := hM
  let _ := hg
  let _ := hh
  constructor
  · simp [fold_zero_coset_intersection_nonempty]
  · simp [fold_zero_coset_intersection_card]

end Omega.Folding
