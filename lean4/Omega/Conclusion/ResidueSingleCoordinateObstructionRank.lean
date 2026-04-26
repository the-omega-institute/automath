import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Conclusion

/-- Concrete rank formula for the single-coordinate obstruction kernel at Fibonacci modulus. -/
def paper_conclusion_residue_single_coordinate_obstruction_rank_statement (m k : ℕ) : Prop :=
  let M := Nat.fib (m + 2)
  let g := Nat.fib (Nat.gcd (m + 2) (k + 1))
  (Omega.Folding.translationKernelCharacterFrequencies M (Nat.fib (k + 1))).card =
    if Even (M / g) then g else 0

/-- Paper label: `thm:conclusion-residue-single-coordinate-obstruction-rank`. -/
theorem paper_conclusion_residue_single_coordinate_obstruction_rank (m k : ℕ) :
    paper_conclusion_residue_single_coordinate_obstruction_rank_statement m k := by
  dsimp [paper_conclusion_residue_single_coordinate_obstruction_rank_statement]
  let M := Nat.fib (m + 2)
  let w := Nat.fib (k + 1)
  let g := Nat.fib (Nat.gcd (m + 2) (k + 1))
  have hMpos : 0 < M := by
    dsimp [M]
    exact Nat.fib_pos.mpr (by omega)
  have hFourier := Omega.Folding.paper_fold_translation_kernel_fourier_sgM M w hMpos
  have hgcd : Nat.gcd M w = g := by
    dsimp [M, w, g]
    simpa using (Omega.fib_gcd (m + 2) (k + 1))
  by_cases hEven : Even (M / g)
  · have hStepEven : Even (Omega.Folding.sgMStep M w) := by
      simpa [Omega.Folding.sgMStep, hgcd] using hEven
    have hcard :
        (Omega.Folding.translationKernelCharacterFrequencies M w).card = Nat.gcd M w :=
      hFourier.2.2.2.2 hStepEven
    rw [if_pos hEven]
    simpa [hgcd] using hcard
  · have hStepOdd : ¬ Even (Omega.Folding.sgMStep M w) := by
      simpa [Omega.Folding.sgMStep, hgcd] using hEven
    have hcard :
        (Omega.Folding.translationKernelCharacterFrequencies M w).card = 0 := by
      simp [Omega.Folding.translationKernelCharacterFrequencies, hStepOdd]
    rw [if_neg hEven]
    simpa using hcard

end Omega.Conclusion
