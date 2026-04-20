import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Folding.FoldMultiplicityGroupAlgebra

open scoped BigOperators

namespace Omega.Folding

/-- The `j`-th factor in the fold-multiplicity Fourier product at the half-modulus frequency. -/
noncomputable def foldMultiplicityHalfModulusFactor (m : ℕ) (j : Fin m) : ℂ :=
  1 + Complex.exp ((Nat.fib (j.1 + 2) : ℂ) * (Real.pi * Complex.I))

/-- The fold-multiplicity Fourier transform evaluated at the half-modulus character. -/
noncomputable def foldMultiplicityFourierAtHalfModulus (m : ℕ) : ℂ :=
  ∏ j : Fin m, foldMultiplicityHalfModulusFactor m j

/-- When `F_{m+2}` is even, the half-modulus character is legitimate and the first Fibonacci factor
already vanishes, forcing the whole fold spectrum to vanish.
    thm:fold-spectrum-parity-zero -/
theorem paper_fold_spectrum_parity_zero (m : ℕ)
    (hEven : Even (Omega.Folding.foldMultiplicityModulus m)) :
    foldMultiplicityFourierAtHalfModulus m = 0 := by
  have hmpos : 0 < m := by
    cases m with
    | zero =>
        simp [Omega.Folding.foldMultiplicityModulus] at hEven
    | succ n =>
        exact Nat.succ_pos _
  have hfactor0 : foldMultiplicityHalfModulusFactor m ⟨0, hmpos⟩ = 0 := by
    calc
      foldMultiplicityHalfModulusFactor m ⟨0, hmpos⟩
          = 1 + Complex.exp (Real.pi * Complex.I) := by
              simp [foldMultiplicityHalfModulusFactor]
      _ = 0 := by simp [Complex.exp_pi_mul_I]
  unfold foldMultiplicityFourierAtHalfModulus
  exact (Finset.prod_eq_zero_iff).2 ⟨⟨0, hmpos⟩, Finset.mem_univ _, hfactor0⟩

end Omega.Folding
