import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinMinsectorDensityPhiMinus2
import Omega.Folding.KilloFoldBinNormalizedGaugeDeficiency

open Filter
open scoped Topology goldenRatio

namespace Omega.Folding

/-- Paper-facing bridge statement for `cor:fold-bin-recover-2pi`: the normalized gauge
deficiency rewrites `log C_m` as `log (2 * π)` plus the explicit Stirling--Bernoulli correction,
and the minimum-sector density input used to control the averaged error is the audited
`φ⁻²` limit. -/
def fold_bin_recover_2pi_statement : Prop :=
  (∀ (C : ℕ → ℝ) (R m : ℕ),
    Real.log (killoFoldBinNormalizationConstant C m) =
      Real.log (2 * Real.pi) + killoFoldBinGaugeDeficiencyMainTerm R m +
        killoFoldBinGaugeDeficiencyRemainder C R m) ∧
    ∀ (sectorCard totalCard : ℕ → ℕ),
      (∀ m : ℕ, sectorCard m = Nat.fib m) →
      (∀ m : ℕ, totalCard m = Nat.fib (m + 2)) →
        Tendsto (fun m : ℕ => foldBinMinsectorDensity (sectorCard m) (totalCard m)) atTop
          (𝓝 ((φ : ℝ)⁻¹ * φ⁻¹))

theorem paper_fold_bin_recover_2pi : fold_bin_recover_2pi_statement := by
  refine ⟨?_, ?_⟩
  · intro C R m
    exact
      (paper_killo_fold_bin_normalized_gauge_deficiency C R m).1.symm.trans
        (paper_killo_fold_bin_normalized_gauge_deficiency C R m).2
  · intro sectorCard totalCard hsector htotal
    exact (paper_fold_bin_minsector_density_phi_minus2 sectorCard totalCard hsector htotal).2

end Omega.Folding
