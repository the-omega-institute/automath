import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointHeatProbeRstarRegularVariationTail

open Filter
open scoped Topology

namespace Omega.Zeta

/-- The endpoint atom at `-1`. -/
def xiEndpointAtomMass (mMinusOne : ℝ) : ℝ :=
  mMinusOne

/-- The complementary heat-kernel contribution in the concrete one-parameter tail model. -/
noncomputable def xiEndpointComplementTerm (tailMass : ℝ) (N : ℕ) : ℝ :=
  xiEndpointHeatProbeRegularVariationTerm tailMass 0 N

/-- The endpoint heat-kernel coefficient obtained by separating the atom at `-1`. -/
noncomputable def xiEndpointHeatCoefficient (mMinusOne tailMass : ℝ) (N : ℕ) : ℝ :=
  xiEndpointAtomMass mMinusOne + xiEndpointComplementTerm tailMass N

private lemma xiEndpointComplementTerm_antitone (tailMass : ℝ) (htail : 0 ≤ tailMass) :
    Antitone (xiEndpointComplementTerm tailMass) := by
  intro m n hmn
  unfold xiEndpointComplementTerm xiEndpointHeatProbeRegularVariationTerm
  have hm_pos : (0 : ℝ) < m + 1 := by positivity
  have hmn' : (m + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  have hrecip : 1 / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := one_div_le_one_div_of_le hm_pos hmn'
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hrecip htail

private lemma xiEndpointComplementTerm_tendsto_zero (tailMass : ℝ) :
    Tendsto (xiEndpointComplementTerm tailMass) atTop (𝓝 0) := by
  unfold xiEndpointComplementTerm xiEndpointHeatProbeRegularVariationTerm
  have hconst : Tendsto (fun _ : ℕ => tailMass) atTop (𝓝 tailMass) := tendsto_const_nhds
  have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (hconst.mul hdiv)

/-- Splitting the endpoint measure into the atom at `-1` plus the complement gives an exact
decomposition of `a_N`, the remainder is antitone when the complementary mass is nonnegative, its
distance from the atom tends to `0`, and the existing endpoint-tail normalization theorem recovers
the complementary mass.
    cor:xi-endpoint-atom-separation -/
theorem paper_xi_endpoint_atom_separation (mMinusOne tailMass : ℝ) (htail : 0 ≤ tailMass) :
    (∀ N : ℕ, xiEndpointHeatCoefficient mMinusOne tailMass N =
      xiEndpointAtomMass mMinusOne + xiEndpointComplementTerm tailMass N) ∧
      Antitone (fun N : ℕ =>
        xiEndpointHeatCoefficient mMinusOne tailMass N - xiEndpointAtomMass mMinusOne) ∧
      Tendsto (fun N : ℕ =>
        xiEndpointHeatCoefficient mMinusOne tailMass N - xiEndpointAtomMass mMinusOne) atTop
        (𝓝 0) ∧
      Tendsto (fun N : ℕ =>
        ((N + 1 : ℝ) *
          (xiEndpointHeatCoefficient mMinusOne tailMass N - xiEndpointAtomMass mMinusOne))) atTop
        (𝓝 tailMass) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    rfl
  · intro m n hmn
    simpa [xiEndpointHeatCoefficient, xiEndpointAtomMass] using
      xiEndpointComplementTerm_antitone tailMass htail hmn
  · have htail0 := xiEndpointComplementTerm_tendsto_zero tailMass
    simpa [xiEndpointHeatCoefficient, xiEndpointAtomMass] using htail0
  · have hnorm :
        Tendsto
          (fun N : ℕ => ((N + 1 : ℝ) ^ (0 + 1)) *
            xiEndpointHeatProbeRegularVariationTerm tailMass 0 N) atTop (𝓝 tailMass) :=
        (paper_xi_endpoint_heat_probe_rstar_regular_variation_tail 1 mMinusOne tailMass 0
          (by positivity)).2
    simpa [xiEndpointHeatCoefficient, xiEndpointAtomMass, xiEndpointComplementTerm] using hnorm

end Omega.Zeta
