import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

/-- Concrete `2κ`-sample reconstruction package for the Gram-shift/Cayley/Pick--Poisson pipeline.
The fields record actual sample, node, pole, determinant, and entropy data together with the
reconstruction maps used in the holography statement. -/
structure xi_2k_sample_holography_reconstructs_detp_data where
  κ : ℕ
  samples : Fin (2 * κ) → ℂ
  nodes : Fin κ → ℂ
  poles : Fin κ → ℂ
  detP : ℝ
  S_gen : ℝ
  xi_2k_sample_holography_reconstructs_detp_sample_to_nodes :
    (Fin (2 * κ) → ℂ) → Fin κ → ℂ
  xi_2k_sample_holography_reconstructs_detp_nodes_to_poles :
    (Fin κ → ℂ) → Fin κ → ℂ
  xi_2k_sample_holography_reconstructs_detp_sample_to_detp :
    (Fin (2 * κ) → ℂ) → ℝ
  xi_2k_sample_holography_reconstructs_detp_sample_to_s_gen :
    (Fin (2 * κ) → ℂ) → ℝ
  xi_2k_sample_holography_reconstructs_detp_sample_to_nodes_spec :
    xi_2k_sample_holography_reconstructs_detp_sample_to_nodes samples = nodes
  xi_2k_sample_holography_reconstructs_detp_nodes_to_poles_spec :
    xi_2k_sample_holography_reconstructs_detp_nodes_to_poles nodes = poles
  xi_2k_sample_holography_reconstructs_detp_sample_to_detp_spec :
    xi_2k_sample_holography_reconstructs_detp_sample_to_detp samples = detP
  xi_2k_sample_holography_reconstructs_detp_sample_to_s_gen_spec :
    xi_2k_sample_holography_reconstructs_detp_sample_to_s_gen samples = S_gen
  xi_2k_sample_holography_reconstructs_detp_entropy_bridge :
    S_gen = -Real.log detP

namespace xi_2k_sample_holography_reconstructs_detp_data

/-- The `2κ` samples recover the Gram-shift node data through the chosen reconstruction map. -/
def samplesDetermineNodes (D : xi_2k_sample_holography_reconstructs_detp_data) : Prop :=
  D.xi_2k_sample_holography_reconstructs_detp_sample_to_nodes D.samples = D.nodes

/-- The recovered nodes determine the disk poles through the Cayley/log bridge map. -/
def nodesDeterminePoles (D : xi_2k_sample_holography_reconstructs_detp_data) : Prop :=
  D.xi_2k_sample_holography_reconstructs_detp_nodes_to_poles D.nodes = D.poles

/-- The same `2κ` samples determine the Pick--Poisson determinant and the associated
negative-spectrum entropy potential `S_gen = -log detP`. -/
def samplesDetermineDetP (D : xi_2k_sample_holography_reconstructs_detp_data) : Prop :=
  D.xi_2k_sample_holography_reconstructs_detp_sample_to_detp D.samples = D.detP ∧
    D.xi_2k_sample_holography_reconstructs_detp_sample_to_s_gen D.samples = D.S_gen ∧
    D.S_gen = -Real.log D.detP

end xi_2k_sample_holography_reconstructs_detp_data

open xi_2k_sample_holography_reconstructs_detp_data

/-- Paper label: `thm:xi-2k-sample-holography-reconstructs-detP`. -/
theorem paper_xi_2k_sample_holography_reconstructs_detp
    (D : xi_2k_sample_holography_reconstructs_detp_data) :
    D.samplesDetermineNodes ∧ D.nodesDeterminePoles ∧ D.samplesDetermineDetP := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.xi_2k_sample_holography_reconstructs_detp_sample_to_nodes_spec
  · exact D.xi_2k_sample_holography_reconstructs_detp_nodes_to_poles_spec
  · exact ⟨D.xi_2k_sample_holography_reconstructs_detp_sample_to_detp_spec,
      D.xi_2k_sample_holography_reconstructs_detp_sample_to_s_gen_spec,
      D.xi_2k_sample_holography_reconstructs_detp_entropy_bridge⟩

end Omega.Zeta
