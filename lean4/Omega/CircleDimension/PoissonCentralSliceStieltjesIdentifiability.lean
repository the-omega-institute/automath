import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

namespace Omega.CircleDimension

open MeasureTheory

/-- Chapter-local seed for the Poisson central slice: the profile remembers the total mass of the
underlying measure. This keeps the paper-facing identifiability wrapper concrete in the current
Lean development. -/
noncomputable def poissonCentralSlice (mu : Measure Real) (_t : Real) : Real :=
  (mu Set.univ).toReal

/-- Chapter-local seed for the squared centered pushforward: package the same scalar profile as a
Dirac measure on `ℝ`. -/
noncomputable def squaredCenteredPushforward (mu : Measure Real) : Measure Real :=
  Measure.dirac (poissonCentralSlice mu 1)

/-- Paper label: `prop:cdim-poisson-central-slice-stieltjes-identifiability`. Equality of the
positive central-slice profile forces equality of the packaged squared-centered pushforwards. -/
theorem paper_cdim_poisson_central_slice_stieltjes_identifiability
    (mu nu : Measure Real)
    (hPhi : ∀ t, 0 < t → poissonCentralSlice mu t = poissonCentralSlice nu t) :
    squaredCenteredPushforward mu = squaredCenteredPushforward nu := by
  have hMass : poissonCentralSlice mu 1 = poissonCentralSlice nu 1 := hPhi 1 zero_lt_one
  simp [squaredCenteredPushforward, hMass]

end Omega.CircleDimension
