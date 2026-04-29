import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.StokesEnergyCellSamplingConcentration

namespace Omega.Conclusion

/-- Concrete finite cell-sampling data for the multiscale Stokes random-sampling certificate. -/
structure ConclusionStokesRandomSamplingCertificateData where
  cellCount : ℕ
  sampleCount : ℕ
  amplitudeBound : ℝ
  cellBoundaryScale : ℝ
  epsilon : ℝ
  delta : ℝ
  samples : Fin cellCount → Fin sampleCount → ℝ
  expectation : Fin cellCount → ℝ
  cellCount_pos : 0 < cellCount
  sampleCount_pos : 0 < sampleCount
  sample_scale_pos : 0 < cellBoundaryScale * amplitudeBound
  epsilon_pos : 0 < epsilon
  delta_pos : 0 < delta
  delta_le_two_cellCount : delta ≤ 2 * cellCount
  sample_bound :
    ∀ C j, 0 ≤ samples C j ∧
      samples C j ≤ (cellBoundaryScale * amplitudeBound) ^ 2
  cell_hoeffding :
    ∀ C, stokesHoeffdingEvent (samples C) (expectation C) epsilon
  sample_size_bound :
    (cellBoundaryScale * amplitudeBound) ^ 2 *
        Real.log (((2 : ℝ) * cellCount) / delta) ≤
      2 * sampleCount * epsilon ^ 2

namespace ConclusionStokesRandomSamplingCertificateData

/-- The per-cell deterministic concentration bounds together with the finite-family union bound. -/
def uniform_tail_bound (D : ConclusionStokesRandomSamplingCertificateData) : Prop :=
  (∀ C : Fin D.cellCount,
    |stokesCellEmpiricalMean (D.samples C) - D.expectation C| ≤ D.epsilon) ∧
    2 * (D.cellCount : ℝ) *
        Real.exp
          (-(2 * D.sampleCount * D.epsilon ^ 2) /
            (D.cellBoundaryScale * D.amplitudeBound) ^ 2) ≤
      D.delta

end ConclusionStokesRandomSamplingCertificateData

open ConclusionStokesRandomSamplingCertificateData

/-- Paper label: `prop:conclusion-stokes-random-sampling-certificate`. Each cell inherits the
existing cell-sampling concentration estimate with scale `(|∂C|/h^{k+1}) B`, and the finite dyadic
cell family contributes the factor `M_m` through the union bound. -/
theorem paper_conclusion_stokes_random_sampling_certificate
    (D : ConclusionStokesRandomSamplingCertificateData) : D.uniform_tail_bound := by
  refine ⟨?_, ?_⟩
  · intro C
    have hcell :=
      paper_conclusion_stokes_energy_cell_sampling_concentration
        (hn := D.sampleCount_pos)
        (M := D.cellBoundaryScale * D.amplitudeBound)
        (hPow := 1)
        (cellVolume := 1)
        (expectation := D.expectation C)
        (radius := D.epsilon)
        (X := D.samples C)
        (hX := D.sample_bound C)
        (hHoeffding := D.cell_hoeffding C)
    simpa [stokesRescaledDeviation] using hcell.2
  · have hlog_arg_pos : 0 < (((2 : ℝ) * D.cellCount) / D.delta) := by
      have hcellCount_pos : (0 : ℝ) < D.cellCount := by
        exact_mod_cast D.cellCount_pos
      have hnum_pos : 0 < (2 : ℝ) * D.cellCount := by positivity
      exact div_pos hnum_pos D.delta_pos
    have hscale_sq_pos : 0 < (D.cellBoundaryScale * D.amplitudeBound) ^ 2 := by
      exact sq_pos_of_pos D.sample_scale_pos
    have hsamples :
        Real.log (((2 : ℝ) * D.cellCount) / D.delta) ≤
          (2 * D.sampleCount * D.epsilon ^ 2) /
            (D.cellBoundaryScale * D.amplitudeBound) ^ 2 := by
      exact (le_div_iff₀ hscale_sq_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using D.sample_size_bound
    have hexponent_le :
        -(2 * D.sampleCount * D.epsilon ^ 2) /
            (D.cellBoundaryScale * D.amplitudeBound) ^ 2 ≤
          -Real.log (((2 : ℝ) * D.cellCount) / D.delta) := by
      have hneg : -((2 * D.sampleCount * D.epsilon ^ 2) /
            (D.cellBoundaryScale * D.amplitudeBound) ^ 2) ≤
          -Real.log (((2 : ℝ) * D.cellCount) / D.delta) := neg_le_neg hsamples
      simpa [neg_div] using hneg
    have hexp_le :
        Real.exp
            (-(2 * D.sampleCount * D.epsilon ^ 2) /
              (D.cellBoundaryScale * D.amplitudeBound) ^ 2) ≤
          Real.exp (-Real.log (((2 : ℝ) * D.cellCount) / D.delta)) := by
      exact Real.exp_le_exp.mpr hexponent_le
    have hcellCount_ne : ((D.cellCount : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt D.cellCount_pos
    calc
      2 * (D.cellCount : ℝ) *
          Real.exp
            (-(2 * D.sampleCount * D.epsilon ^ 2) /
              (D.cellBoundaryScale * D.amplitudeBound) ^ 2)
          ≤
        2 * (D.cellCount : ℝ) * Real.exp (-Real.log (((2 : ℝ) * D.cellCount) / D.delta)) := by
            gcongr
      _ = D.delta := by
            rw [Real.exp_neg, Real.exp_log hlog_arg_pos]
            field_simp [hcellCount_ne, D.delta_pos.ne']

end Omega.Conclusion
