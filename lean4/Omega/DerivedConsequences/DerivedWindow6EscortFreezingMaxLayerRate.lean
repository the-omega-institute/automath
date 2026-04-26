import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.FoldResidualTime.Window6FixedFreezingLaw

namespace Omega.DerivedConsequences

open Filter Omega.FoldResidualTime
open scoped Topology

/-- The audited window-`6` escort partition function. -/
def derived_window6_escort_freezing_max_layer_rate_partition (q : ℕ) : ℝ :=
  window6FiberMomentSum q

/-- Normalized escort mass on the `d = 2` layer. -/
noncomputable def derived_window6_escort_freezing_max_layer_rate_M2 (q : ℕ) : ℝ :=
  8 * (2 : ℝ) ^ q / derived_window6_escort_freezing_max_layer_rate_partition q

/-- Normalized escort mass on the `d = 3` layer. -/
noncomputable def derived_window6_escort_freezing_max_layer_rate_M3 (q : ℕ) : ℝ :=
  4 * (3 : ℝ) ^ q / derived_window6_escort_freezing_max_layer_rate_partition q

/-- Normalized escort mass on the maximal `d = 4` layer. -/
noncomputable def derived_window6_escort_freezing_max_layer_rate_M4 (q : ℕ) : ℝ :=
  9 * (4 : ℝ) ^ q / derived_window6_escort_freezing_max_layer_rate_partition q

/-- Conditional mass of one maximal-fiber point after renormalizing by the total `d = 4` mass. -/
noncomputable def derived_window6_escort_freezing_max_layer_rate_conditional_point_mass
    (q : ℕ) : ℝ :=
  ((4 : ℝ) ^ q / derived_window6_escort_freezing_max_layer_rate_partition q) /
    derived_window6_escort_freezing_max_layer_rate_M4 q

private lemma derived_window6_escort_freezing_max_layer_rate_partition_pos (q : ℕ) :
    0 < derived_window6_escort_freezing_max_layer_rate_partition q := by
  unfold derived_window6_escort_freezing_max_layer_rate_partition window6FiberMomentSum
  positivity

private lemma derived_window6_escort_freezing_max_layer_rate_M4_eq_window6MaxLayerEscortMass (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_M4 q = window6MaxLayerEscortMass q := by
  rfl

private lemma derived_window6_escort_freezing_max_layer_rate_M4_formula (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_M4 q = (1 + window6FreezingCorrection q)⁻¹ := by
  rcases paper_frt_window6_fixed_freezing_law with
    ⟨_hmoment, hfactor, _hlog, _hcorr, _hlogcorr, _hescort⟩
  unfold derived_window6_escort_freezing_max_layer_rate_M4
    derived_window6_escort_freezing_max_layer_rate_partition
  rw [hfactor q]
  have hlead : (9 * (4 : ℝ) ^ q) ≠ 0 := by
    positivity
  have hcorr : (1 + window6FreezingCorrection q) ≠ 0 := by
    have : 0 < 1 + window6FreezingCorrection q := by
      unfold window6FreezingCorrection
      positivity
    linarith
  field_simp [hlead, hcorr]

private lemma derived_window6_escort_freezing_max_layer_rate_M3_formula (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_M3 q =
      ((4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q) *
        derived_window6_escort_freezing_max_layer_rate_M4 q := by
  rw [derived_window6_escort_freezing_max_layer_rate_M4_formula]
  rcases paper_frt_window6_fixed_freezing_law with
    ⟨_hmoment, hfactor, _hlog, _hcorr, _hlogcorr, _hescort⟩
  unfold derived_window6_escort_freezing_max_layer_rate_M3
    derived_window6_escort_freezing_max_layer_rate_partition
  rw [hfactor q]
  have hlead : (9 * (4 : ℝ) ^ q) ≠ 0 := by
    positivity
  have hcorr : (1 + window6FreezingCorrection q) ≠ 0 := by
    have : 0 < 1 + window6FreezingCorrection q := by
      unfold window6FreezingCorrection
      positivity
    linarith
  have hpow : (4 : ℝ) ^ q * (3 / 4 : ℝ) ^ q = (3 : ℝ) ^ q := by
    rw [← mul_pow]
    norm_num
  field_simp [hlead, hcorr]
  rw [← hpow]

private lemma derived_window6_escort_freezing_max_layer_rate_M2_formula (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_M2 q =
      ((8 / 9 : ℝ) * (1 / 2 : ℝ) ^ q) *
        derived_window6_escort_freezing_max_layer_rate_M4 q := by
  rw [derived_window6_escort_freezing_max_layer_rate_M4_formula]
  rcases paper_frt_window6_fixed_freezing_law with
    ⟨_hmoment, hfactor, _hlog, _hcorr, _hlogcorr, _hescort⟩
  unfold derived_window6_escort_freezing_max_layer_rate_M2
    derived_window6_escort_freezing_max_layer_rate_partition
  rw [hfactor q]
  have hlead : (9 * (4 : ℝ) ^ q) ≠ 0 := by
    positivity
  have hcorr : (1 + window6FreezingCorrection q) ≠ 0 := by
    have : 0 < 1 + window6FreezingCorrection q := by
      unfold window6FreezingCorrection
      positivity
    linarith
  have hpow : (4 : ℝ) ^ q * (1 / 2 : ℝ) ^ q = (2 : ℝ) ^ q := by
    rw [← mul_pow]
    norm_num
  field_simp [hlead, hcorr]
  rw [← hpow]

private lemma derived_window6_escort_freezing_max_layer_rate_sum (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_M2 q +
        derived_window6_escort_freezing_max_layer_rate_M3 q +
        derived_window6_escort_freezing_max_layer_rate_M4 q =
      1 := by
  unfold derived_window6_escort_freezing_max_layer_rate_M2
    derived_window6_escort_freezing_max_layer_rate_M3
    derived_window6_escort_freezing_max_layer_rate_M4
  have hpart : derived_window6_escort_freezing_max_layer_rate_partition q ≠ 0 := by
    exact (derived_window6_escort_freezing_max_layer_rate_partition_pos q).ne'
  field_simp [derived_window6_escort_freezing_max_layer_rate_partition, hpart]
  rfl

private lemma derived_window6_escort_freezing_max_layer_rate_conditional_uniformity (q : ℕ) :
    derived_window6_escort_freezing_max_layer_rate_conditional_point_mass q = 1 / 9 := by
  unfold derived_window6_escort_freezing_max_layer_rate_conditional_point_mass
    derived_window6_escort_freezing_max_layer_rate_M4
  have hpart : derived_window6_escort_freezing_max_layer_rate_partition q ≠ 0 := by
    exact (derived_window6_escort_freezing_max_layer_rate_partition_pos q).ne'
  have hfour : ((4 : ℝ) ^ q) ≠ 0 := by positivity
  field_simp [hpart, hfour]

/-- Paper label: `thm:derived-window6-escort-freezing-max-layer-rate`. -/
theorem paper_derived_window6_escort_freezing_max_layer_rate :
    (∀ q : ℕ,
      derived_window6_escort_freezing_max_layer_rate_M2 q +
          derived_window6_escort_freezing_max_layer_rate_M3 q +
          derived_window6_escort_freezing_max_layer_rate_M4 q =
        1) ∧
    (∀ q : ℕ,
      derived_window6_escort_freezing_max_layer_rate_M4 q = (1 + window6FreezingCorrection q)⁻¹) ∧
    (∀ q : ℕ,
      derived_window6_escort_freezing_max_layer_rate_M3 q =
        ((4 / 9 : ℝ) * (3 / 4 : ℝ) ^ q) *
          derived_window6_escort_freezing_max_layer_rate_M4 q) ∧
    (∀ q : ℕ,
      derived_window6_escort_freezing_max_layer_rate_M2 q =
        ((8 / 9 : ℝ) * (1 / 2 : ℝ) ^ q) *
          derived_window6_escort_freezing_max_layer_rate_M4 q) ∧
    Filter.Tendsto derived_window6_escort_freezing_max_layer_rate_M4 Filter.atTop (nhds 1) ∧
    (∀ q : ℕ,
      derived_window6_escort_freezing_max_layer_rate_conditional_point_mass q = 1 / 9) := by
  rcases paper_frt_window6_fixed_freezing_law with
    ⟨_hmoment, _hfactor, _hlog, _hcorr, _hlogcorr, hescort⟩
  refine ⟨derived_window6_escort_freezing_max_layer_rate_sum,
    derived_window6_escort_freezing_max_layer_rate_M4_formula,
    derived_window6_escort_freezing_max_layer_rate_M3_formula,
    derived_window6_escort_freezing_max_layer_rate_M2_formula, ?_, ?_⟩
  · simpa [derived_window6_escort_freezing_max_layer_rate_M4_eq_window6MaxLayerEscortMass] using hescort
  · exact derived_window6_escort_freezing_max_layer_rate_conditional_uniformity

end Omega.DerivedConsequences
