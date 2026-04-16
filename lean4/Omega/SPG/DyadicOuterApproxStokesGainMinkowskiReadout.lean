import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- The dyadic decay profile attached to codimension `ambientDim - minkowskiDim`. -/
noncomputable def dyadicOuterApproxDecay (ambientDim minkowskiDim : ℝ) (m : ℕ) : ℝ :=
  2 ^ (-(m : ℝ) * (ambientDim - minkowskiDim))

/-- Paper-facing abstract wrapper for the Stokes gain and single-probe Minkowski readout.
    thm:spg-dyadic-outer-approx-stokes-gain-minkowski-readout -/
theorem paper_spg_dyadic_outer_approx_stokes_gain_minkowski_readout
    (ambientDim minkowskiDim envelopeConst dωNorm probeReadout : ℝ)
    (flux volume probeFlux : ℕ → ℝ)
    (hNorm : 0 ≤ dωNorm)
    (hStokes : ∀ m, |flux m| ≤ dωNorm * volume m)
    (hEnvelope : ∀ m,
      volume m ≤ envelopeConst * dyadicOuterApproxDecay ambientDim minkowskiDim m)
    (hProbe : ∀ m, probeFlux m = volume m)
    (hReadout : minkowskiDim = ambientDim + probeReadout) :
    (∀ m, |flux m| ≤
      (dωNorm * envelopeConst) * dyadicOuterApproxDecay ambientDim minkowskiDim m) ∧
      (∀ m, probeFlux m = volume m) ∧
      minkowskiDim = ambientDim + probeReadout := by
  refine ⟨?_, hProbe, hReadout⟩
  intro m
  calc
    |flux m| ≤ dωNorm * volume m := hStokes m
    _ ≤ dωNorm * (envelopeConst * dyadicOuterApproxDecay ambientDim minkowskiDim m) := by
          exact mul_le_mul_of_nonneg_left (hEnvelope m) hNorm
    _ = (dωNorm * envelopeConst) * dyadicOuterApproxDecay ambientDim minkowskiDim m := by
          ring

end Omega.SPG
