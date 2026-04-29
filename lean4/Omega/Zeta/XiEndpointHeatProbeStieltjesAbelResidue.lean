import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

/-- Two-point compression support: the endpoint `1` and one non-endpoint point `s`. -/
def xi_endpoint_heat_probe_stieltjes_abel_residue_nodes (s : ℝ) : Fin 2 → ℝ
  | 0 => 1
  | 1 => s

/-- Endpoint and non-endpoint atom weights. -/
def xi_endpoint_heat_probe_stieltjes_abel_residue_weights
    (endpointMass interiorMass : ℝ) : Fin 2 → ℝ
  | 0 => endpointMass
  | 1 => interiorMass

/-- Transported finite-support Stieltjes moments. -/
def xi_endpoint_heat_probe_stieltjes_abel_residue_moment
    (endpointMass interiorMass s : ℝ) (N : ℕ) : ℝ :=
  endpointMass + interiorMass * s ^ N

/-- Stieltjes transform of the two-atom pushforward measure. -/
noncomputable def xi_endpoint_heat_probe_stieltjes_abel_residue_genfun
    (endpointMass interiorMass s z : ℝ) : ℝ :=
  endpointMass / (1 - z) + interiorMass / (1 - z * s)

/-- Removable Abel-residue expression after multiplying the generating function by `1 - z`. -/
noncomputable def xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr
    (endpointMass interiorMass s z : ℝ) : ℝ :=
  endpointMass + (1 - z) * (interiorMass / (1 - z * s))

/-- Paper label: `prop:xi-endpoint-heat-probe-stieltjes-abel-residue`.  For a concrete
two-atom pushforward measure, the moments are transported to `[0,1]`, the generating function is
the finite Stieltjes transform, and the Abel residue recovers the endpoint atom. -/
theorem paper_xi_endpoint_heat_probe_stieltjes_abel_residue
    (endpointMass interiorMass s : ℝ) (hendpoint : 0 ≤ endpointMass)
    (hinterior : 0 ≤ interiorMass) (hs_nonneg : 0 ≤ s) (hs_lt : s < 1) :
    (∀ i : Fin 2,
        0 ≤ xi_endpoint_heat_probe_stieltjes_abel_residue_nodes s i ∧
          xi_endpoint_heat_probe_stieltjes_abel_residue_nodes s i ≤ 1) ∧
      (∀ i : Fin 2,
        0 ≤ xi_endpoint_heat_probe_stieltjes_abel_residue_weights endpointMass interiorMass i) ∧
      (∀ N : ℕ,
        xi_endpoint_heat_probe_stieltjes_abel_residue_moment endpointMass interiorMass s N =
          ∑ i : Fin 2,
            xi_endpoint_heat_probe_stieltjes_abel_residue_weights endpointMass interiorMass i *
              xi_endpoint_heat_probe_stieltjes_abel_residue_nodes s i ^ N) ∧
      (∀ z : ℝ, z ≠ 1 → z * s ≠ 1 →
        xi_endpoint_heat_probe_stieltjes_abel_residue_genfun endpointMass interiorMass s z =
          ∑ i : Fin 2,
            xi_endpoint_heat_probe_stieltjes_abel_residue_weights endpointMass interiorMass i /
              (1 - z * xi_endpoint_heat_probe_stieltjes_abel_residue_nodes s i)) ∧
      (∀ z : ℝ, z ≠ 1 →
        (1 - z) *
            xi_endpoint_heat_probe_stieltjes_abel_residue_genfun endpointMass interiorMass s z =
          xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr
            endpointMass interiorMass s z) ∧
      Tendsto
        (fun z : ℝ =>
          xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr
            endpointMass interiorMass s z) (𝓝 1) (𝓝 endpointMass) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [xi_endpoint_heat_probe_stieltjes_abel_residue_nodes]
    · exact ⟨hs_nonneg, hs_lt.le⟩
  · intro i
    fin_cases i
    · simpa [xi_endpoint_heat_probe_stieltjes_abel_residue_weights] using hendpoint
    · simpa [xi_endpoint_heat_probe_stieltjes_abel_residue_weights] using hinterior
  · intro N
    simp [xi_endpoint_heat_probe_stieltjes_abel_residue_moment,
      xi_endpoint_heat_probe_stieltjes_abel_residue_weights,
      xi_endpoint_heat_probe_stieltjes_abel_residue_nodes, Fin.sum_univ_two]
  · intro z hz hzs
    simp [xi_endpoint_heat_probe_stieltjes_abel_residue_genfun,
      xi_endpoint_heat_probe_stieltjes_abel_residue_weights,
      xi_endpoint_heat_probe_stieltjes_abel_residue_nodes, Fin.sum_univ_two]
  · intro z hz
    have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
    calc
      (1 - z) *
          xi_endpoint_heat_probe_stieltjes_abel_residue_genfun endpointMass interiorMass s z
          =
            (1 - z) * (endpointMass / (1 - z)) +
              (1 - z) * (interiorMass / (1 - z * s)) := by
            rw [xi_endpoint_heat_probe_stieltjes_abel_residue_genfun, mul_add]
      _ = xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr
            endpointMass interiorMass s z := by
            rw [xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr]
            field_simp [hden]
  · have hleft : Tendsto (fun z : ℝ => (1 - z) * (interiorMass / (1 - z * s))) (𝓝 1)
        (𝓝 (0 * (interiorMass / (1 - 1 * s)))) := by
      have hzero : Tendsto (fun z : ℝ => 1 - z) (𝓝 1) (𝓝 0) := by
        simpa using (tendsto_const_nhds.sub tendsto_id : Tendsto (fun z : ℝ => 1 - z)
          (𝓝 1) (𝓝 (1 - 1)))
      have hdenlim : Tendsto (fun z : ℝ => 1 - z * s) (𝓝 1) (𝓝 (1 - 1 * s)) := by
        simpa using (tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds) :
          Tendsto (fun z : ℝ => 1 - z * s) (𝓝 1) (𝓝 (1 - 1 * s)))
      have hquot : Tendsto (fun z : ℝ => interiorMass / (1 - z * s)) (𝓝 1)
          (𝓝 (interiorMass / (1 - 1 * s))) := by
        exact tendsto_const_nhds.div hdenlim (by
          have hpos : 0 < 1 - 1 * s := by linarith
          exact ne_of_gt hpos)
      exact hzero.mul hquot
    have hmain :
        Tendsto
          (fun z : ℝ =>
            endpointMass + (1 - z) * (interiorMass / (1 - z * s))) (𝓝 1)
          (𝓝 (endpointMass + 0 * (interiorMass / (1 - 1 * s)))) :=
      tendsto_const_nhds.add hleft
    simpa [xi_endpoint_heat_probe_stieltjes_abel_residue_residueExpr] using hmain

end Omega.Zeta
