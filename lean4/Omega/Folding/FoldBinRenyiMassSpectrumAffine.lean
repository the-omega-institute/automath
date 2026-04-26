import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinRenyiRateCollapse

open Filter

namespace Omega.Folding

/-- The explicit prefactor predicted by the affine Rényi mass spectrum. -/
noncomputable def fold_bin_renyi_mass_spectrum_affine_leadingConstant (q : ℝ) : ℝ :=
  (Real.goldenRatio + Real.goldenRatio ^ (-q)) / Real.sqrt 5

/-- The affine mass-spectrum model singled out by the paper. -/
noncomputable def fold_bin_renyi_mass_spectrum_affine_model (q : ℝ) (m : ℕ) : ℝ :=
  fold_bin_renyi_mass_spectrum_affine_leadingConstant q *
    Real.goldenRatio ^ ((1 - q) * (m : ℝ))

/-- The linear Rényi slope in natural logarithmic normalization. -/
noncomputable def fold_bin_renyi_mass_spectrum_affine_slope (q : ℝ) : ℝ :=
  (q - 1) * Real.log Real.goldenRatio

/-- Paper label: `thm:fold-bin-renyi-mass-spectrum-affine`. The affine model keeps the closed-form
prefactor visible and packages the linear Rényi slope as an immediate consequence of the already
verified entropy-rate collapse to `log φ`. -/
theorem paper_fold_bin_renyi_mass_spectrum_affine (q : ℝ) (hq : 0 < q) :
    0 < fold_bin_renyi_mass_spectrum_affine_leadingConstant q ∧
      fold_bin_renyi_mass_spectrum_affine_leadingConstant q =
        (Real.goldenRatio + Real.goldenRatio ^ (-q)) / Real.sqrt 5 ∧
      (∀ m : ℕ,
        fold_bin_renyi_mass_spectrum_affine_model q m =
          fold_bin_renyi_mass_spectrum_affine_leadingConstant q *
            Real.goldenRatio ^ ((1 - q) * (m : ℝ))) ∧
      Tendsto (fun m : ℕ => (q - 1) * foldBinRenyiEntropyRate q m) atTop
        (nhds (fold_bin_renyi_mass_spectrum_affine_slope q)) := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · unfold fold_bin_renyi_mass_spectrum_affine_leadingConstant
    positivity
  · intro m
    rfl
  · simpa [fold_bin_renyi_mass_spectrum_affine_slope] using
      Filter.Tendsto.const_mul (q - 1) (paper_fold_bin_renyi_rate_collapse q hq)

end Omega.Folding
