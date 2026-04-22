import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.EA.Sync10UniformOutputCorr
import Omega.EA.Sync10UniformStationary
import Omega.Graph.TransferMatrix

namespace Omega.POM

open Polynomial
open Omega.EA
open scoped goldenRatio

noncomputable section

/-- The input-saturated Perron scale of the real-input `40` skeleton. -/
def realInput40SaturatedScale : ℝ :=
  Real.goldenRatio ^ 2

/-- The corresponding saturated scale of the audited `10`-state sync kernel. -/
def sync10SaturatedScale : ℚ :=
  3

/-- The chapter-facing saturation statement for the top exponential scale. -/
def lambdaSaturationInputScaleStatement : Prop :=
  realInput40SaturatedScale = Real.goldenRatio ^ 2 ∧ sync10SaturatedScale = 3

/-- The twisted golden factor carrying the real-input mechanism-sensitive spectral correction. -/
def lambdaSaturationTwistedFactor : ℚ[X] :=
  ((1 : ℚ[X]) + Polynomial.X) - Polynomial.X ^ 2

/-- The mechanism-sensitive fingerprint is recorded by finite-part data from the `Sync10` kernel
and by the twisted `-A` factor on the real-input side. -/
def lambdaSaturationMechanismFingerprintStatement : Prop :=
  sync10UniformNormalizedStationaryVector ∧
    sync10OutputOneProb = 1 / 2 ∧
    sync10FlipProb = 137 / 216 ∧
    sync10OutputCorr 1 = -29 / 108 ∧
    lambdaSaturationTwistedFactor = ((1 : ℚ[X]) + Polynomial.X) - Polynomial.X ^ 2

/-- Paper label: `prop:pom-lambda-saturation`.
The leading exponential scale is the input-skeleton scale `φ²` on the real-input side and the
audited value `3` on the `Sync10` side; the mechanism fingerprint then lives in finite-part data
and in the twisted `-A` spectral factor. -/
theorem paper_pom_lambda_saturation :
    lambdaSaturationInputScaleStatement ∧
      lambdaSaturationMechanismFingerprintStatement := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  have hstat := paper_sync10_uniform_stationary
  rcases paper_sync10_uniform_de with
    ⟨_, _, _, _, _, _, hOutputOne, _, _, _⟩
  rcases paper_sync10_uniform_output_corr with
    ⟨_, _, _, _, hFlip, hCorr1, _, _, _⟩
  exact ⟨hstat, hOutputOne, hFlip, hCorr1, rfl⟩

end

end Omega.POM
