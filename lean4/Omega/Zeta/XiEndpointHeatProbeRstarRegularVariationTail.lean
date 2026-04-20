import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Endpoint atom contribution after factoring out the dominant radius `rStar^N`. -/
def xiEndpointHeatProbeAtomicTerm (rStar atom : ℝ) (N : ℕ) : ℝ :=
  atom * rStar ^ N

/-- A concrete regularly varying endpoint tail with polynomial exponent `k + 1`. -/
noncomputable def xiEndpointHeatProbeRegularVariationTerm (tailConstant : ℝ) (k N : ℕ) : ℝ :=
  tailConstant / (N + 1 : ℝ) ^ (k + 1)

set_option maxHeartbeats 400000 in
/-- Concrete endpoint-heat probe asymptotics: after dividing out the dominant endpoint factor,
the atomic contribution converges to its endpoint mass, while the regularly varying remainder has
the expected polynomial normalization.
    thm:xi-endpoint-heat-probe-rstar-regular-variation-tail -/
theorem paper_xi_endpoint_heat_probe_rstar_regular_variation_tail
    (rStar atom tailConstant : ℝ) (k : ℕ) (hrStar : 0 < rStar) :
    Tendsto (fun N : ℕ => xiEndpointHeatProbeAtomicTerm rStar atom N / rStar ^ N) atTop
      (𝓝 atom) ∧
      Tendsto
        (fun N : ℕ =>
          ((N + 1 : ℝ) ^ (k + 1)) * xiEndpointHeatProbeRegularVariationTerm tailConstant k N)
        atTop (𝓝 tailConstant) := by
  refine ⟨?_, ?_⟩
  · have hfun :
        (fun N : ℕ => xiEndpointHeatProbeAtomicTerm rStar atom N / rStar ^ N) =
          fun _ => atom := by
      funext N
      have hpow : rStar ^ N ≠ 0 := pow_ne_zero N hrStar.ne'
      simp [xiEndpointHeatProbeAtomicTerm, hpow]
    rw [hfun]
    exact tendsto_const_nhds
  · have hfun :
        (fun N : ℕ =>
          ((N + 1 : ℝ) ^ (k + 1)) * xiEndpointHeatProbeRegularVariationTerm tailConstant k N) =
          fun _ => tailConstant := by
      funext N
      have hpow : ((N + 1 : ℝ) ^ (k + 1)) ≠ 0 := by
        have hbase : (0 : ℝ) < (N + 1 : ℝ) := by
          positivity
        exact pow_ne_zero (k + 1) (ne_of_gt hbase)
      rw [xiEndpointHeatProbeRegularVariationTerm]
      field_simp [hpow]
    rw [hfun]
    exact tendsto_const_nhds

end Omega.Zeta
