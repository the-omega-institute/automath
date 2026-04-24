import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldOrbitSpectrumIdentifiabilityHistogram

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The first gauge-volume moment of the orbit histogram. -/
def foldOrbitGaugeVolume {m : ℕ} (N : FoldOrbitHistogram m) : ℚ :=
  ∑ d, N d * (foldOrbitDegree d : ℚ)

/-- The `q`-th power-sum moment of the orbit histogram degrees. -/
def foldOrbitPowerSum {m : ℕ} (N : FoldOrbitHistogram m) (q : ℕ) : ℚ :=
  ∑ d, N d * (foldOrbitDegree d : ℚ) ^ q

/-- The orbit spectrum identifies the histogram, hence every gauge-volume and power-sum functional
built from those counts. -/
def FoldOrbitSpectrumReconstructsGaugeVolumeMoments {m : ℕ} (N : FoldOrbitHistogram m) : Prop :=
  FoldOrbitFactorizationFormula N ∧
    FoldOrbitTriangularRecursion N ∧
      ∀ M : FoldOrbitHistogram m, (∀ q : ℕ, foldOrbitLogHCoeff N q = foldOrbitLogHCoeff M q) →
        foldOrbitGaugeVolume M = foldOrbitGaugeVolume N ∧
          ∀ q : ℕ, foldOrbitPowerSum M q = foldOrbitPowerSum N q

/-- Recovering the histogram counts from the orbit spectrum makes every gauge-volume and power-sum
moment a direct substitution of those recovered counts.
    cor:op-algebra-fold-orbit-spectrum-reconstructs-gauge-volume-moments -/
theorem paper_op_algebra_fold_orbit_spectrum_reconstructs_gauge_volume_moments
    {m : ℕ} (N : FoldOrbitHistogram m) : FoldOrbitSpectrumReconstructsGaugeVolumeMoments N := by
  rcases paper_op_algebra_fold_orbit_spectrum_identifiability_histogram N with
    ⟨hFactor, hTri, hUnique⟩
  refine ⟨hFactor, hTri, ?_⟩
  intro M hcoeff
  have hMN : M = N := hUnique M hcoeff
  subst hMN
  refine ⟨rfl, ?_⟩
  intro q
  rfl

end Omega.OperatorAlgebra
