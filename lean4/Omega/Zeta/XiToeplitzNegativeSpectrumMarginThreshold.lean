import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-toeplitz-negative-spectrum-margin-threshold`.

Finite-dimensional perturbation form of the Toeplitz negative-spectrum certificate.  The
`referenceEigenvalue` coordinates model the eigenvalues of `-P` on the defect block, the
`perturbedEigenvalue` coordinates model the corresponding finite Toeplitz block after the Weyl
operator-norm error estimate, `hIndexLower` is the min-max lower bound from the `kappa` stable
negative directions, and `hFiniteDefectUpper` is the finite-defect upper bound. -/
theorem paper_xi_toeplitz_negative_spectrum_margin_threshold
    (kappa negativeIndex : ℕ) (lambdaMin : ℝ)
    (referenceEigenvalue perturbedEigenvalue : Fin kappa → ℝ)
    (hLambdaMin : 0 < lambdaMin)
    (hReference : ∀ i, referenceEigenvalue i ≤ -lambdaMin)
    (hWeyl : ∀ i, |perturbedEigenvalue i - referenceEigenvalue i| ≤ lambdaMin / 2)
    (hIndexLower : kappa ≤ negativeIndex)
    (hFiniteDefectUpper : negativeIndex ≤ kappa) :
    negativeIndex = kappa ∧ 0 < lambdaMin / 2 ∧
      ∀ i, perturbedEigenvalue i ≤ -lambdaMin / 2 := by
  refine ⟨le_antisymm hFiniteDefectUpper hIndexLower, by linarith, ?_⟩
  intro i
  have hErrorUpper :
      perturbedEigenvalue i - referenceEigenvalue i ≤ lambdaMin / 2 :=
    le_trans (le_abs_self _) (hWeyl i)
  have hRef := hReference i
  linarith

end Omega.Zeta
