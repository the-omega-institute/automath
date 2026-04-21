import Mathlib.Tactic
import Omega.Folding.FoldCollisionZeroReduction
import Omega.Folding.MaxFiber

namespace Omega.Folding

/-- The maximal fold fiber is bounded by the total number of words contributing to the fold law. -/
theorem maxFiberMultiplicity_le_wordcount (m : ℕ) : Omega.X.maxFiberMultiplicity m ≤ 2 ^ m := by
  obtain ⟨x, hx⟩ := Omega.X.maxFiberMultiplicity_achieved m
  calc
    Omega.X.maxFiberMultiplicity m = Omega.X.fiberMultiplicity x := by rw [hx]
    _ ≤ ∑ y : Omega.X m, Omega.X.fiberMultiplicity y :=
      Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
    _ = 2 ^ m := Omega.X.fiberMultiplicity_sum_eq_pow m

/-- The fold-collision gap is sandwiched between the normalized max-fiber lower bound and the
zero-reduction upper bound after both are rewritten against the same uniform baseline
`1 / F_{m+2}`.
    thm:fold-collision-sandwich -/
theorem paper_fold_collision_sandwich (m : ℕ) :
    (((Omega.X.maxFiberMultiplicity m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) -
        1 / (Nat.fib (m + 2) : ℚ) ≤
      foldMultiplicityCollisionProbability m - 1 / (Nat.fib (m + 2) : ℚ)) ∧
    (foldMultiplicityCollisionProbability m - 1 / (Nat.fib (m + 2) : ℚ) ≤
      ((Nat.fib (m + 2) - 1 : ℚ) / Nat.fib (m + 2))) := by
  have hmax_le : Omega.X.maxFiberMultiplicity m ≤ 2 ^ m := maxFiberMultiplicity_le_wordcount m
  have hnum_le_nat : Omega.X.maxFiberMultiplicity m ^ 2 ≤ (2 ^ m) ^ 2 := by
    exact Nat.pow_le_pow_left hmax_le 2
  have hnum_le :
      ((Omega.X.maxFiberMultiplicity m : ℚ) ^ 2) ≤ ((2 ^ m : ℚ) ^ 2) := by
    exact_mod_cast hnum_le_nat
  have hden_pos : (0 : ℚ) < (2 : ℚ) ^ (2 * m) := by positivity
  have hword_ratio :
      ((2 ^ m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) = 1 := by
    rw [show ((2 ^ m : ℚ) ^ 2) = (2 : ℚ) ^ (2 * m) by
      calc
        ((2 ^ m : ℚ) ^ 2) = (2 : ℚ) ^ (m * 2) := by rw [pow_mul]
        _ = (2 : ℚ) ^ (2 * m) := by simp [Nat.mul_comm]]
    exact div_self hden_pos.ne'
  have hratio_le_one :
      ((Omega.X.maxFiberMultiplicity m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) ≤ 1 := by
    calc
      ((Omega.X.maxFiberMultiplicity m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) ≤
          ((2 ^ m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) := by
            exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
      _ = 1 := hword_ratio
  have hcollision : foldMultiplicityCollisionProbability m = 1 := by
    exact (paper_fold_collision_spectrum m).2.1
  have hfib_pos : 0 < Nat.fib (m + 2) := by
    exact Nat.fib_pos.mpr (by omega)
  have hfib_ne : (Nat.fib (m + 2) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfib_pos)
  have hbaseline :
      1 - 1 / (Nat.fib (m + 2) : ℚ) = ((Nat.fib (m + 2) - 1 : ℚ) / Nat.fib (m + 2)) := by
    field_simp [hfib_ne]
  have hupper0 :
      foldMultiplicityCollisionProbability m ≤ 1 - (0 : ℚ) / Nat.fib (m + 2) := by
    simpa using paper_fold_collision_zero_reduction m 0 (Nat.fib (m + 2)) rfl
  constructor
  · calc
      ((Omega.X.maxFiberMultiplicity m : ℚ) ^ 2) / (2 : ℚ) ^ (2 * m) -
          1 / (Nat.fib (m + 2) : ℚ) ≤
        1 - 1 / (Nat.fib (m + 2) : ℚ) := by
          linarith
      _ = foldMultiplicityCollisionProbability m - 1 / (Nat.fib (m + 2) : ℚ) := by
        rw [hcollision]
  · calc
      foldMultiplicityCollisionProbability m - 1 / (Nat.fib (m + 2) : ℚ) ≤
          (1 - (0 : ℚ) / Nat.fib (m + 2)) - 1 / (Nat.fib (m + 2) : ℚ) := by
            linarith
      _ = 1 - 1 / (Nat.fib (m + 2) : ℚ) := by simp
      _ = ((Nat.fib (m + 2) - 1 : ℚ) / Nat.fib (m + 2)) := hbaseline

end Omega.Folding
