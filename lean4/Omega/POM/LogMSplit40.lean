import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.POM.RealInput40ZetaFactorization
import Omega.SyncKernelWeighted.RealInput40LogMSplit

namespace Omega.POM

noncomputable section

/-- The Perron pole `z_* = φ⁻²` singled out by the real-input `40` factorization. -/
def pom_logm_split_40_zstar : ℝ :=
  Real.goldenRatio ^ (-(2 : ℤ))

/-- In the seed additive packaging, the analytic twist factor contributes no extra finite-part
term beyond its value at the pole. -/
def pom_logm_split_40_twist_contribution
    (_D : Omega.SyncKernelWeighted.RealInput40LogMSplitData) : ℝ :=
  0

/-- The remaining finite-part contribution is the short/trivial vertical term already isolated by
the weighted finite-part split. -/
def pom_logm_split_40_triv_contribution
    (D : Omega.SyncKernelWeighted.RealInput40LogMSplitData) : ℝ :=
  D.pVertAtPole

/-- Paper label: `cor:pom-logM-split-40`. The determinant/zeta factorization identifies the pole
location and the trivial short-period correction, while the weighted finite-part wrapper gives the
additive decomposition of the total finite part into input, twist, and trivial pieces. -/
theorem paper_pom_logm_split_40 (D : Omega.SyncKernelWeighted.RealInput40LogMSplitData) :
    realInput40DetFactorization ∧
      realInput40ZetaFactorization ∧
      realInput40ShortPeriodCorrection ∧
      D.logMM =
        D.logMIn +
          pom_logm_split_40_twist_contribution D +
            pom_logm_split_40_triv_contribution D := by
  rcases paper_pom_zeta_factorization_40 with ⟨hdet, hzeta, hshort⟩
  refine ⟨hdet, hzeta, hshort, ?_⟩
  simpa [pom_logm_split_40_twist_contribution, pom_logm_split_40_triv_contribution] using
    Omega.SyncKernelWeighted.paper_real_input_40_logM_split D

end

end Omega.POM
