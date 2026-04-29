import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic
import Omega.Folding.FoldResonanceDocagne

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- The finite reversed cosine product obtained from the resonant Fibonacci frequency. -/
def foldCriticalResonanceReversedCosineProduct (m : ℕ) : ℝ :=
  Finset.prod (Finset.Icc 1 m) fun j =>
    |Real.cos (Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2))|

/-- Lean-side package for the finite resonance rewrite behind the critical-resonance constant:
each resonant cosine factor rewrites to the reversed Fibonacci product term from the d'Ocagne
identity, and the resulting finite product is nonnegative. -/
def FoldCriticalResonanceConstantLaw : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ j : ℕ, 1 ≤ j → j ≤ m →
      |Real.cos (Real.pi * ((Nat.fib m : ℝ) * Nat.fib (j + 1)) / Nat.fib (m + 2))| =
        |Real.cos (Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2))|) ∧
    0 ≤ foldCriticalResonanceReversedCosineProduct m

private theorem fold_resonance_abs_cos_rewrite
    (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m) :
    |Real.cos (Real.pi * ((Nat.fib m : ℝ) * Nat.fib (j + 1)) / Nat.fib (m + 2))| =
      |Real.cos (Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2))| := by
  have hdoc := paper_fold_resonance_docagne m j hm hj hjm
  have hEqInt :
      (Nat.fib m : Int) * (Nat.fib (j + 1) : Int) =
        (Nat.fib (j - 1) : Int) * (Nat.fib (m + 2) : Int) +
          ((-1 : Int) ^ (j + 1)) * (Nat.fib (m + 1 - j) : Int) := by
    simpa [add_comm] using eq_add_of_sub_eq hdoc
  have hEq :
      (Nat.fib m : ℝ) * (Nat.fib (j + 1) : ℝ) =
        (Nat.fib (j - 1) : ℝ) * (Nat.fib (m + 2) : ℝ) +
          (((-1 : Int) ^ (j + 1)) * (Nat.fib (m + 1 - j) : Int) : ℝ) := by
    exact_mod_cast hEqInt
  have hFibPos : 0 < (Nat.fib (m + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hFibNe : (Nat.fib (m + 2) : ℝ) ≠ 0 := by
    exact ne_of_gt hFibPos
  let y : ℝ :=
    Real.pi * (((-1 : ℝ) ^ (j + 1)) * (Nat.fib (m + 1 - j) : ℝ)) / Nat.fib (m + 2)
  have harg :
      Real.pi * ((Nat.fib m : ℝ) * Nat.fib (j + 1)) / Nat.fib (m + 2) =
        (Nat.fib (j - 1) : ℝ) * Real.pi + y := by
    dsimp [y]
    rw [hEq]
    field_simp [hFibNe]
    norm_num
  have hshift :
      |Real.cos (Real.pi * ((Nat.fib m : ℝ) * Nat.fib (j + 1)) / Nat.fib (m + 2))| =
        |Real.cos y| := by
    rw [harg]
    have hcos :
        Real.cos (y + (Nat.fib (j - 1) : ℝ) * Real.pi) =
          (-1 : ℝ) ^ Nat.fib (j - 1) * Real.cos y := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        Real.cos_add_nat_mul_pi y (Nat.fib (j - 1))
    rw [show (Nat.fib (j - 1) : ℝ) * Real.pi + y = y + (Nat.fib (j - 1) : ℝ) * Real.pi by ring]
    rw [hcos, abs_mul, abs_neg_one_pow, one_mul]
  by_cases hEven : Even (j + 1)
  · rw [hshift]
    have hsR : (-1 : ℝ) ^ (j + 1) = 1 := hEven.neg_one_pow
    have hy :
        y = Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2) := by
      dsimp [y]
      rw [hsR]
      ring
    rw [hy]
  · rw [hshift]
    have hOdd : Odd (j + 1) := Nat.not_even_iff_odd.mp hEven
    have hsR : (-1 : ℝ) ^ (j + 1) = -1 := hOdd.neg_one_pow
    have hy :
        y = -(Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2)) := by
      dsimp [y]
      rw [hsR]
      ring
    rw [hy, Real.cos_neg]

/-- Paper label: `thm:fold-critical-resonance-constant`.
This Lean package records the exact d'Ocagne-based reversal of the finite resonant cosine factors
and the positivity of the resulting reversed product. -/
theorem paper_fold_critical_resonance_constant : FoldCriticalResonanceConstantLaw := by
  intro m hm
  refine ⟨?_, ?_⟩
  · intro j hj hjm
    exact fold_resonance_abs_cos_rewrite m j hm hj hjm
  · unfold foldCriticalResonanceReversedCosineProduct
    exact Finset.prod_nonneg fun j _ => abs_nonneg _

end

end Omega.Folding
