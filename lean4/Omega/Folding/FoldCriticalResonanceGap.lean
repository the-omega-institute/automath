import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Tactic
import Omega.Folding.FoldCollisionSpectrum
import Omega.Folding.FoldCriticalResonanceConstant

namespace Omega.Folding

open scoped BigOperators

noncomputable section

private theorem foldCriticalResonanceReversedCosineProduct_sq_le_one (m : ℕ) :
    foldCriticalResonanceReversedCosineProduct m ^ 2 ≤ 1 := by
  have hnonneg : 0 ≤ foldCriticalResonanceReversedCosineProduct m := by
    unfold foldCriticalResonanceReversedCosineProduct
    exact Finset.prod_nonneg fun j _ => abs_nonneg _
  have hle :
      foldCriticalResonanceReversedCosineProduct m ≤ 1 := by
    unfold foldCriticalResonanceReversedCosineProduct
    refine Finset.prod_le_one ?_ ?_
    · intro j hj
      exact abs_nonneg _
    · intro j hj
      simpa using Real.abs_cos_le_one (Real.pi * (Nat.fib (m + 1 - j) : ℝ) / Nat.fib (m + 2))
  nlinarith

/-- Paper label: `cor:fold-critical-resonance-gap`.
The two conjugate Fibonacci resonances contribute a positive correction over the uniform
baseline `1 / F_{m+2}`. -/
theorem paper_fold_critical_resonance_gap (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / Nat.fib (m + 2) +
        2 * foldCriticalResonanceReversedCosineProduct m ^ 2 / Nat.fib (m + 2) ≤
      (foldMultiplicityCollisionProbability m : ℝ) := by
  have hcollisionQ : foldMultiplicityCollisionProbability m = 1 :=
    (paper_fold_collision_spectrum m).2.1
  have hcollision : (foldMultiplicityCollisionProbability m : ℝ) = 1 := by
    exact_mod_cast hcollisionQ
  rw [hcollision]
  by_cases hm1 : m = 1
  · subst hm1
    norm_num [foldCriticalResonanceReversedCosineProduct]
  · have hm2 : 2 ≤ m := by omega
    have hprod : foldCriticalResonanceReversedCosineProduct m ^ 2 ≤ 1 :=
      foldCriticalResonanceReversedCosineProduct_sq_le_one m
    have hfib_ge : (3 : ℝ) ≤ Nat.fib (m + 2) := by
      have hmono : Nat.fib 4 ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
      norm_num at hmono
      exact_mod_cast hmono
    have hfib_pos : (0 : ℝ) < Nat.fib (m + 2) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    have hnum :
        1 + 2 * foldCriticalResonanceReversedCosineProduct m ^ 2 ≤ Nat.fib (m + 2) := by
      nlinarith
    have hden_ne : (Nat.fib (m + 2) : ℝ) ≠ 0 := ne_of_gt hfib_pos
    have hrewrite :
        (1 : ℝ) / Nat.fib (m + 2) +
            2 * foldCriticalResonanceReversedCosineProduct m ^ 2 / Nat.fib (m + 2) =
          (1 + 2 * foldCriticalResonanceReversedCosineProduct m ^ 2) / Nat.fib (m + 2) := by
      field_simp [hden_ne]
    have htop :
        (1 + 2 * foldCriticalResonanceReversedCosineProduct m ^ 2) / Nat.fib (m + 2) ≤
          (Nat.fib (m + 2) : ℝ) / Nat.fib (m + 2) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hfib_pos)
    have hone : (Nat.fib (m + 2) : ℝ) / Nat.fib (m + 2) = 1 := by
      exact div_self hden_ne
    rw [hrewrite]
    simpa [hone] using htop

end

end Omega.Folding
