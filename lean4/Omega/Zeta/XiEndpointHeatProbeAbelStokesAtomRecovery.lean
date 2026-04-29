import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Omega.Zeta.XiEndpointAtomSeparation

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Concrete data for the endpoint heat-probe Abel/Stokes package. The endpoint atom and monotone
tail come from the existing separation theorem, while the spectral-gap parameter controls the
exponential tail estimate. -/
structure XiEndpointHeatProbeAbelStokesData where
  endpointAtom : ℝ
  tailMass : ℝ
  tailMass_nonneg : 0 ≤ tailMass
  spectralGap : ℝ
  spectralGap_nonneg : 0 ≤ spectralGap
  spectralGap_lt_one : spectralGap < 1
  spectralGapAmplitude : ℝ

/-- The separated endpoint coefficient sequence. -/
noncomputable def XiEndpointHeatProbeAbelStokesData.endpointSequence
    (D : XiEndpointHeatProbeAbelStokesData) (N : ℕ) : ℝ :=
  xiEndpointHeatCoefficient D.endpointAtom D.tailMass N

/-- The atom-generated Abel series. -/
noncomputable def XiEndpointHeatProbeAbelStokesData.abelSeries
    (D : XiEndpointHeatProbeAbelStokesData) (r : ℝ) : ℕ → ℝ :=
  fun N => xiEndpointAtomMass D.endpointAtom * r ^ N

/-- The Cesàro mean of the endpoint sequence. -/
noncomputable def XiEndpointHeatProbeAbelStokesData.cesaroMean
    (D : XiEndpointHeatProbeAbelStokesData) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, D.endpointSequence i

/-- The exponentially damped spectral-gap tail. -/
noncomputable def XiEndpointHeatProbeAbelStokesData.spectralGapTail
    (D : XiEndpointHeatProbeAbelStokesData) (N : ℕ) : ℝ :=
  D.spectralGapAmplitude * D.spectralGap ^ N

/-- The Abel/Stokes generating function is the convergent geometric series coming from the
separated endpoint atom. -/
def XiEndpointHeatProbeAbelStokesData.abelStokesGeneratingFunction
    (D : XiEndpointHeatProbeAbelStokesData) : Prop :=
  ∀ r : ℝ, |r| < 1 →
    Summable (D.abelSeries r) ∧
      (∑' n : ℕ, D.abelSeries r n) =
        xiEndpointAtomMass D.endpointAtom * (1 - r)⁻¹

/-- The Abel limit of the endpoint sequence recovers the endpoint atom. -/
def XiEndpointHeatProbeAbelStokesData.abelLimitRecoversEndpointAtom
    (D : XiEndpointHeatProbeAbelStokesData) : Prop :=
  Tendsto D.endpointSequence atTop (𝓝 (xiEndpointAtomMass D.endpointAtom))

/-- The Cesàro means recover the same endpoint atom. -/
def XiEndpointHeatProbeAbelStokesData.cesaroMeanRecoversEndpointAtom
    (D : XiEndpointHeatProbeAbelStokesData) : Prop :=
  Tendsto D.cesaroMean atTop (𝓝 (xiEndpointAtomMass D.endpointAtom))

/-- The spectral-gap tail is uniformly bounded by its initial amplitude. -/
def XiEndpointHeatProbeAbelStokesData.exponentialTailBound
    (D : XiEndpointHeatProbeAbelStokesData) : Prop :=
  ∀ N : ℕ, |D.spectralGapTail N| ≤ |D.spectralGapAmplitude|

/-- Paper label: `thm:xi-endpoint-heat-probe-abel-stokes-atom-recovery`. -/
theorem paper_xi_endpoint_heat_probe_abel_stokes_atom_recovery
    (D : XiEndpointHeatProbeAbelStokesData) :
    D.abelStokesGeneratingFunction ∧ D.abelLimitRecoversEndpointAtom ∧
      D.cesaroMeanRecoversEndpointAtom ∧ D.exponentialTailBound := by
  have hsep := paper_xi_endpoint_atom_separation D.endpointAtom D.tailMass D.tailMass_nonneg
  have habel : D.abelLimitRecoversEndpointAtom := by
    have hdiff :
        Tendsto
          (fun N : ℕ =>
            xiEndpointHeatCoefficient D.endpointAtom D.tailMass N - xiEndpointAtomMass D.endpointAtom)
          atTop (𝓝 0) :=
      hsep.2.2.1
    have hconst :
        Tendsto (fun _ : ℕ => xiEndpointAtomMass D.endpointAtom) atTop
          (𝓝 (xiEndpointAtomMass D.endpointAtom)) :=
      tendsto_const_nhds
    have hsum :
        Tendsto
          (fun N : ℕ =>
            xiEndpointAtomMass D.endpointAtom +
              (xiEndpointHeatCoefficient D.endpointAtom D.tailMass N -
                xiEndpointAtomMass D.endpointAtom))
          atTop (𝓝 (xiEndpointAtomMass D.endpointAtom)) := by
      simpa using hconst.add hdiff
    simpa [XiEndpointHeatProbeAbelStokesData.endpointSequence, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using hsum
  refine ⟨?_, habel, ?_, ?_⟩
  · intro r hr
    refine ⟨Summable.mul_left _ (summable_geometric_of_abs_lt_one hr), ?_⟩
    calc
      ∑' n : ℕ, D.abelSeries r n
          = (∑' n : ℕ, r ^ n) * xiEndpointAtomMass D.endpointAtom := by
              simp [XiEndpointHeatProbeAbelStokesData.abelSeries, tsum_mul_right, mul_comm]
      _ = (1 - r)⁻¹ * xiEndpointAtomMass D.endpointAtom := by
        rw [tsum_geometric_of_abs_lt_one hr]
      _ = xiEndpointAtomMass D.endpointAtom * (1 - r)⁻¹ := by ring
  · simpa [XiEndpointHeatProbeAbelStokesData.cesaroMean] using habel.cesaro
  · intro N
    have hpow_nonneg : 0 ≤ D.spectralGap ^ N := pow_nonneg D.spectralGap_nonneg N
    have hpow_le_one : D.spectralGap ^ N ≤ 1 := by
      exact pow_le_one₀ D.spectralGap_nonneg D.spectralGap_lt_one.le
    calc
      |D.spectralGapTail N| = |D.spectralGapAmplitude| * D.spectralGap ^ N := by
        rw [XiEndpointHeatProbeAbelStokesData.spectralGapTail, abs_mul, abs_of_nonneg hpow_nonneg]
      _ ≤ |D.spectralGapAmplitude| * 1 := by
        exact mul_le_mul_of_nonneg_left hpow_le_one (abs_nonneg _)
      _ = |D.spectralGapAmplitude| := by ring

end Omega.Zeta
