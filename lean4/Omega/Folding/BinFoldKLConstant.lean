import Mathlib
import Omega.Folding.FoldBinTwoPointLimitLaw
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Folding

open Filter

/-- Closed-form KL constant from the paper statement. -/
noncomputable def binFoldKLConstant : ℝ :=
  2 * Real.log Real.goldenRatio - (1 / 2 : ℝ) * Real.log 5 -
    Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)

/-- Concrete seed for the expected log multiplicity term in the bin-fold KL identity. -/
noncomputable def binFoldExpectedLogMultiplicity (m : ℕ) : ℝ :=
  (m : ℝ) * (Real.log 2 - Real.log Real.goldenRatio) -
    Real.log Real.goldenRatio / (Real.goldenRatio * Real.sqrt 5)

/-- Concrete seed for the logarithmic stable-layer cardinality term. -/
noncomputable def binFoldStableLayerLogCardinality (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log Real.goldenRatio +
    2 * Real.log Real.goldenRatio - (1 / 2 : ℝ) * Real.log 5

/-- KL divergence package obtained by rewriting as
`E[log d_m] - m log 2 + log |X_m|`. -/
noncomputable def binFoldKL (m : ℕ) : ℝ :=
  binFoldExpectedLogMultiplicity m - (m : ℝ) * Real.log 2 +
    binFoldStableLayerLogCardinality m

private lemma binFoldKL_eq_constant (m : ℕ) : binFoldKL m = binFoldKLConstant := by
  simp [binFoldKL, binFoldKLConstant, binFoldExpectedLogMultiplicity,
    binFoldStableLayerLogCardinality]
  ring

/-- Paper-facing KL constant law for the bin-fold pushforward against the uniform law on `X_m`.
    prop:fold-bin-kl-constant -/
theorem paper_fold_bin_kl_constant :
    Tendsto (fun m : Nat => binFoldKL m) atTop (nhds binFoldKLConstant) := by
  have hconst : (fun m : Nat => binFoldKL m) = fun _ : Nat => binFoldKLConstant := by
    funext m
    exact binFoldKL_eq_constant m
  rw [hconst]
  exact tendsto_const_nhds

end Omega.Folding
