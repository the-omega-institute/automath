import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectationSingularSpectrum
import Omega.OperatorAlgebra.FoldOrbitSpectrumIdentifiabilityHistogram

namespace Omega.OperatorAlgebra

open FoldFiberMultiplicity

/-- Canonical finite fold-fiber model whose multiplicities are the histogram degrees `1, ..., m`.
-/
def foldConditionalExpectationSpectrumModel (m : ℕ) : FoldFiberMultiplicity where
  X := Fin m
  instDecEqX := inferInstance
  instFintypeX := inferInstance
  d := foldOrbitDegree
  d_pos := by
    intro x
    exact Nat.succ_pos x.1

/-- The singular values of the fold conditional expectation recover the multiplicity degrees by
inverse square, and the finite histogram package then makes the degeneracy histogram unique.
    cor:fold-conditional-expectation-spectrum-histogram -/
theorem paper_fold_conditional_expectation_spectrum_histogram {m : ℕ} (N : FoldOrbitHistogram m) :
    let D := foldConditionalExpectationSpectrumModel m
    (∀ x : Fin m, ((D.singularValue x) ^ 2)⁻¹ = foldOrbitDegree x) ∧
      FoldOrbitFactorizationFormula N ∧
      FoldOrbitTriangularRecursion N ∧
      FoldOrbitHistogramUnique N := by
  dsimp
  have hSpec :=
    paper_prop_fold_conditional_expectation_singular_spectrum
      (foldConditionalExpectationSpectrumModel m)
  have hHist := paper_op_algebra_fold_orbit_spectrum_identifiability_histogram N
  refine ⟨?_, hHist.1, hHist.2.1, hHist.2.2⟩
  intro x
  have hsq :
      (foldConditionalExpectationSpectrumModel m).singularValue x ^ 2 =
        1 / (foldOrbitDegree x : ℝ) := by
    exact (hSpec.2.2 x).trans (hSpec.2.1 x)
  have hpos : 0 < (foldOrbitDegree x : ℝ) := by
    exact_mod_cast Nat.succ_pos x.1
  have hdeg : (foldOrbitDegree x : ℝ) ≠ 0 := ne_of_gt hpos
  rw [hsq]
  have hinv : ((1 / (foldOrbitDegree x : ℝ)) : ℝ)⁻¹ = foldOrbitDegree x := by
    field_simp [hdeg]
  exact hinv

end Omega.OperatorAlgebra
