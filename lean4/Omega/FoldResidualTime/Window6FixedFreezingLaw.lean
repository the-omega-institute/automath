import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.FoldResidualTime

/-- Window-6 `q`-moment sum from the fixed fiber histogram
`8·2^q + 4·3^q + 9·4^q`. -/
def window6FiberMomentSum (q : ℕ) : ℝ :=
  8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q

/-- Small correction after factoring out the maximal `d = 4` layer. -/
noncomputable def window6FreezingCorrection (q : ℕ) : ℝ :=
  (8 / 9 : ℝ) * (1 / 2 : ℝ) ^ q + (4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q

/-- Escort mass carried by the maximal `d = 4` layer. -/
noncomputable def window6MaxLayerEscortMass (q : ℕ) : ℝ :=
  (9 * (4 : ℝ) ^ q) / window6FiberMomentSum q

private theorem window6FiberMomentSum_factorization (q : ℕ) :
    window6FiberMomentSum q =
      9 * (4 : ℝ) ^ q * (1 + window6FreezingCorrection q) := by
  unfold window6FiberMomentSum window6FreezingCorrection
  calc
    8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q
        = 9 * (4 : ℝ) ^ q + 8 * ((4 : ℝ) ^ q * (1 / 2 : ℝ) ^ q) +
            4 * ((4 : ℝ) ^ q * (3 / 4 : ℝ) ^ q) := by
            rw [← mul_pow, ← mul_pow]
            norm_num
            ring
    _ = 9 * (4 : ℝ) ^ q * (1 + (8 / 9 : ℝ) * (1 / 2 : ℝ) ^ q + (4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q) := by
          ring
    _ = 9 * (4 : ℝ) ^ q * (1 + window6FreezingCorrection q) := by
          simp [window6FreezingCorrection, add_left_comm, add_comm]

private theorem window6FiberMomentSum_log_decomposition (q : ℕ) :
    Real.log (window6FiberMomentSum q) =
      Real.log 9 + (q : ℝ) * Real.log 4 + Real.log (1 + window6FreezingCorrection q) := by
  rw [window6FiberMomentSum_factorization]
  have h9 : (9 : ℝ) ≠ 0 := by norm_num
  have h4 : ((4 : ℝ) ^ q) ≠ 0 := by exact pow_ne_zero q (by norm_num)
  have hcorr_nonneg : 0 ≤ (window6FreezingCorrection q : ℝ) := by
    unfold window6FreezingCorrection
    positivity
  have hcorr_pos : 0 < (1 + window6FreezingCorrection q : ℝ) := by
    linarith
  have hcorr : (1 + window6FreezingCorrection q : ℝ) ≠ 0 := hcorr_pos.ne'
  rw [Real.log_mul (mul_ne_zero h9 h4) hcorr, Real.log_mul h9 h4]
  have hpow : Real.log ((4 : ℝ) ^ q) = (q : ℝ) * Real.log 4 := by
    simpa using Real.log_rpow (4 : ℝ) q
  simpa [hpow, add_assoc, add_left_comm, add_comm]

private theorem tendsto_window6FreezingCorrection :
    Filter.Tendsto window6FreezingCorrection Filter.atTop (nhds 0) := by
  have hhalf : Filter.Tendsto (fun q : ℕ => ((2 : ℝ)⁻¹) ^ q) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have hthreeFourths :
      Filter.Tendsto (fun q : ℕ => (3 / 4 : ℝ) ^ q) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have h1 :
      Filter.Tendsto (fun q : ℕ => (8 / 9 : ℝ) * ((2 : ℝ)⁻¹) ^ q)
        Filter.atTop (nhds ((8 / 9 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hhalf
  have h2 :
      Filter.Tendsto (fun q : ℕ => (4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q)
        Filter.atTop (nhds ((4 / 9 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hthreeFourths
  have hmain :
      Filter.Tendsto
        (fun q : ℕ => (8 / 9 : ℝ) * ((2 : ℝ)⁻¹) ^ q + (4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q)
        Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  have heq :
      window6FreezingCorrection = fun q : ℕ =>
        (8 / 9 : ℝ) * ((2 : ℝ)⁻¹) ^ q + (4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q := by
    funext q
    simp [window6FreezingCorrection, one_div]
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun q => by simp [heq]) hmain

private theorem tendsto_window6_log_correction :
    Filter.Tendsto (fun q : ℕ => Real.log (1 + window6FreezingCorrection q))
      Filter.atTop (nhds 0) := by
  have hcorr :
      Filter.Tendsto (fun q : ℕ => (1 : ℝ) + window6FreezingCorrection q)
        Filter.atTop (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_window6FreezingCorrection
  have hcorr' :
      Filter.Tendsto (fun q : ℕ => (1 : ℝ) + window6FreezingCorrection q)
        Filter.atTop (nhds 1) := by
    simpa using hcorr
  have hlog :
      Filter.Tendsto (fun q : ℕ => Real.log (1 + window6FreezingCorrection q))
        Filter.atTop (nhds (Real.log 1)) := by
    exact (Real.continuousAt_log one_ne_zero).tendsto.comp hcorr'
  simpa using hlog

private theorem window6MaxLayerEscortMass_eq (q : ℕ) :
    window6MaxLayerEscortMass q = (1 + window6FreezingCorrection q)⁻¹ := by
  unfold window6MaxLayerEscortMass
  rw [window6FiberMomentSum_factorization]
  have hlead : (9 * (4 : ℝ) ^ q : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero q (by norm_num))
  have hcorr_nonneg : 0 ≤ (window6FreezingCorrection q : ℝ) := by
    unfold window6FreezingCorrection
    positivity
  have hcorr_pos : 0 < (1 + window6FreezingCorrection q : ℝ) := by
    linarith
  field_simp [hlead, hcorr_pos.ne']

private theorem tendsto_window6MaxLayerEscortMass :
    Filter.Tendsto window6MaxLayerEscortMass Filter.atTop (nhds 1) := by
  have hcorr :
      Filter.Tendsto (fun q : ℕ => (1 : ℝ) + window6FreezingCorrection q)
        Filter.atTop (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_window6FreezingCorrection
  have hcorr' :
      Filter.Tendsto (fun q : ℕ => (1 : ℝ) + window6FreezingCorrection q)
        Filter.atTop (nhds 1) := by
    simpa using hcorr
  have hinv :
      Filter.Tendsto (fun q : ℕ => (1 + window6FreezingCorrection q)⁻¹)
        Filter.atTop (nhds ((1 : ℝ)⁻¹)) := by
    exact (ContinuousAt.inv₀ continuousAt_id (by norm_num)).tendsto.comp hcorr'
  have hinv' :
      Filter.Tendsto (fun q : ℕ => (1 + window6FreezingCorrection q)⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using hinv
  have heq :
      (fun q : ℕ => window6MaxLayerEscortMass q) =ᶠ[Filter.atTop]
        fun q : ℕ => (1 + window6FreezingCorrection q)⁻¹ :=
    Filter.Eventually.of_forall window6MaxLayerEscortMass_eq
  exact Filter.Tendsto.congr' heq.symm hinv'

/-- Paper-facing fixed-freezing law for the window-6 fiber histogram: exact `q`-moment
decomposition, exact logarithmic splitting, vanishing `log(1+t)` correction, and concentration of
escort mass on the maximal `d = 4` layer.
    prop:frt-window6-fixed-freezing-law -/
theorem paper_frt_window6_fixed_freezing_law :
    (∀ q : ℕ, window6FiberMomentSum q = 8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q) ∧
    (∀ q : ℕ, window6FiberMomentSum q = 9 * (4 : ℝ) ^ q * (1 + window6FreezingCorrection q)) ∧
    (∀ q : ℕ,
      Real.log (window6FiberMomentSum q) =
        Real.log 9 + (q : ℝ) * Real.log 4 + Real.log (1 + window6FreezingCorrection q)) ∧
    Filter.Tendsto window6FreezingCorrection Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun q : ℕ => Real.log (1 + window6FreezingCorrection q))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto window6MaxLayerEscortMass Filter.atTop (nhds 1) := by
  refine ⟨?_, window6FiberMomentSum_factorization, window6FiberMomentSum_log_decomposition,
    tendsto_window6FreezingCorrection, tendsto_window6_log_correction,
    tendsto_window6MaxLayerEscortMass⟩
  intro q
  rfl

end Omega.FoldResidualTime
