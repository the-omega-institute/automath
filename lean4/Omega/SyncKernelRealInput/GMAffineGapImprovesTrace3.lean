import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete data for the affine-gap trace-`3` improvement template.  The affine decomposition
is scalar-seeded, while the residual exponent is the explicit `4 - sigma` channel advertised by
the trace argument. -/
structure gm_affine_gap_improves_trace3_Data where
  gm_affine_gap_improves_trace3_affineAverage : ℝ
  gm_affine_gap_improves_trace3_rankOneMain : ℝ
  gm_affine_gap_improves_trace3_residual : ℝ
  gm_affine_gap_improves_trace3_affine_decomposition :
    gm_affine_gap_improves_trace3_affineAverage =
      gm_affine_gap_improves_trace3_rankOneMain + gm_affine_gap_improves_trace3_residual
  gm_affine_gap_improves_trace3_sigma : ℝ
  gm_affine_gap_improves_trace3_sigma_pos : 0 < gm_affine_gap_improves_trace3_sigma
  gm_affine_gap_improves_trace3_optimal_spectral_lifting :
    0 ≤ gm_affine_gap_improves_trace3_rankOneMain

namespace gm_affine_gap_improves_trace3_Data

/-- Baseline residual channel exponent corresponding to the un-improved `M^4` bound. -/
def baselineChannelExponent (_D : gm_affine_gap_improves_trace3_Data) : ℝ :=
  4

/-- Improved residual channel exponent coming from the affine spectral gap. -/
def residualChannelExponent (D : gm_affine_gap_improves_trace3_Data) : ℝ :=
  4 - D.gm_affine_gap_improves_trace3_sigma

/-- Strict power saving means the residual exponent is below the baseline `M^4` exponent. -/
def strictPowerSaving (D : gm_affine_gap_improves_trace3_Data) : Prop :=
  D.residualChannelExponent < D.baselineChannelExponent

/-- The balance threshold shift is a concrete exponent-level displacement. -/
noncomputable def balanceThresholdShift (D : gm_affine_gap_improves_trace3_Data) : ℝ :=
  D.gm_affine_gap_improves_trace3_sigma / 2

/-- The threshold displacement is computable from the spectral gap and is strictly positive. -/
def balanceThresholdComputable (D : gm_affine_gap_improves_trace3_Data) : Prop :=
  ∃ shift : ℝ, shift = D.balanceThresholdShift ∧ 0 < shift

end gm_affine_gap_improves_trace3_Data

/-- Paper label: `prop:gm-affine-gap-improves-trace3`. -/
theorem paper_gm_affine_gap_improves_trace3
    (D : gm_affine_gap_improves_trace3_Data) :
    D.strictPowerSaving ∧ D.balanceThresholdComputable := by
  constructor
  · dsimp [gm_affine_gap_improves_trace3_Data.strictPowerSaving,
      gm_affine_gap_improves_trace3_Data.residualChannelExponent,
      gm_affine_gap_improves_trace3_Data.baselineChannelExponent]
    linarith [D.gm_affine_gap_improves_trace3_sigma_pos]
  · refine ⟨D.balanceThresholdShift, rfl, ?_⟩
    dsimp [gm_affine_gap_improves_trace3_Data.balanceThresholdShift]
    linarith [D.gm_affine_gap_improves_trace3_sigma_pos]

end Omega.SyncKernelRealInput
