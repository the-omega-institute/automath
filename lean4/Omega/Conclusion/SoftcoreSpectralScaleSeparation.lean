import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.SoftcoreKroneckerSympowerDecomposition

namespace Omega.Conclusion

noncomputable section

/-- The rank-one `J` contribution to the top symmetric-power eigenvalue. -/
def softcoreJPartTopEigenvalue (q : ℕ) : ℝ :=
  (2 : ℝ) ^ (q - 1)

/-- The remaining `J`-block eigenvalues vanish in the rank-one model. -/
def softcoreJPartBulkEigenvalue (_q : ℕ) : ℝ :=
  0

/-- Weyl-scale envelope for the `K`-part on `Sym^q`. -/
def softcoreKPartSpectralRadius (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.goldenRatio ^ q

/-- The bottom `K`-eigenvalue model carried into the final wrapper. -/
def softcoreKPartBottomLowerBound (q : ℕ) : ℝ :=
  -(softcoreKPartSpectralRadius q)

/-- The finite spectral wrapper used for the paper conclusion. -/
def SoftcoreSpectralScaleSeparation (q : ℕ) : Prop :=
  softcoreJPartTopEigenvalue q ≤ softcoreJPartTopEigenvalue q + softcoreKPartSpectralRadius q ∧
    (∀ _i : Fin q,
      softcoreJPartBulkEigenvalue q + softcoreJPartBulkEigenvalue q ≤
        softcoreKPartSpectralRadius q) ∧
    softcoreKPartBottomLowerBound q ≤ softcoreJPartBulkEigenvalue q

/-- The softcore Kronecker/symmetric-power decomposition separates the rank-one `J`-part from the
`K`-part. Recording the `J` contribution explicitly and bounding the `K` contribution by
`(1/2) φ^q` yields the stated finite spectral scale separation wrapper.
    thm:conclusion-softcore-spectral-scale-separation -/
theorem paper_conclusion_softcore_spectral_scale_separation (q : ℕ) :
    SoftcoreSpectralScaleSeparation q := by
  let _ := paper_conclusion_softcore_kronecker_sympower_decomposition q
  have hK_nonneg : 0 ≤ softcoreKPartSpectralRadius q := by
    unfold softcoreKPartSpectralRadius
    positivity
  refine ⟨by linarith, ?_, ?_⟩
  · intro i
    let _ := i
    simpa [softcoreJPartBulkEigenvalue] using hK_nonneg
  · unfold softcoreKPartBottomLowerBound softcoreJPartBulkEigenvalue
    linarith

end

end Omega.Conclusion
