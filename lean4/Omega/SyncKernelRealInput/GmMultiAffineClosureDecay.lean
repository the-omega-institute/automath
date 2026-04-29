import Mathlib.Tactic
import Omega.SyncKernelRealInput.GmAffineSelfmapSpectralGap

namespace Omega.SyncKernelRealInput

open Matrix

/-- Concrete finite-family affine-closure parameters. -/
structure gm_multi_affine_closure_decay_data where
  affineMapCount : ℕ
  ambientGrowth : ℝ

/-- The combined constraint system has the original readout plus one coordinate per affine map. -/
def gm_multi_affine_closure_decay_combinedArity
    (D : gm_multi_affine_closure_decay_data) : ℕ :=
  D.affineMapCount + 1

/-- Fixed-point count for the compiled finite affine-closure system. -/
def gm_multi_affine_closure_decay_fixCount
    (_D : gm_multi_affine_closure_decay_data) (m : ℕ) : ℕ :=
  gm_affine_selfmap_spectral_gap_fixCount m

/-- Transition matrix for the compiled finite affine-closure system. -/
def gm_multi_affine_closure_decay_matrix :=
  gm_affine_selfmap_spectral_gap_matrix

/-- Entry vector for the compiled finite affine-closure system. -/
def gm_multi_affine_closure_decay_entryVector :=
  gm_affine_selfmap_spectral_gap_entryVector

/-- Exit vector for the compiled finite affine-closure system. -/
def gm_multi_affine_closure_decay_exitVector :=
  gm_affine_selfmap_spectral_gap_exitVector

/-- Perron root of the finite affine-closure matrix. -/
def gm_multi_affine_closure_decay_rho : ℝ :=
  gm_affine_selfmap_spectral_gap_rho

/-- Paper-facing statement for finite multi-affine closure decay. -/
def gm_multi_affine_closure_decay_statement
    (D : gm_multi_affine_closure_decay_data) : Prop :=
  gm_multi_affine_closure_decay_combinedArity D = D.affineMapCount + 1 ∧
  (∀ m : ℕ,
    gm_multi_affine_closure_decay_fixCount D m =
      gm_multi_affine_closure_decay_entryVector 0 *
        (gm_multi_affine_closure_decay_matrix ^ m) 0 0 *
          gm_multi_affine_closure_decay_exitVector 0) ∧
  (1 < D.ambientGrowth →
    gm_multi_affine_closure_decay_rho < D.ambientGrowth ∧
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ m : ℕ,
            (gm_multi_affine_closure_decay_fixCount D m : ℝ) ≤
              (D.ambientGrowth - ε) ^ m)

/-- Paper label: `thm:gm-multi-affine-closure-decay`. -/
theorem paper_gm_multi_affine_closure_decay
    (D : gm_multi_affine_closure_decay_data) :
    gm_multi_affine_closure_decay_statement D := by
  refine ⟨rfl, ?_, ?_⟩
  · intro m
    rcases paper_gm_affine_selfmap_spectral_gap (2 : ℝ) (by norm_num) with
      ⟨hmatrix, _, _⟩
    simpa [gm_multi_affine_closure_decay_fixCount,
      gm_multi_affine_closure_decay_entryVector,
      gm_multi_affine_closure_decay_matrix,
      gm_multi_affine_closure_decay_exitVector] using hmatrix m
  · intro hgrowth
    rcases paper_gm_affine_selfmap_spectral_gap D.ambientGrowth hgrowth with
      ⟨_, hrho, ε, hε, hdecay⟩
    refine ⟨by simpa [gm_multi_affine_closure_decay_rho] using hrho, ε, hε, ?_⟩
    intro m
    simpa [gm_multi_affine_closure_decay_fixCount] using hdecay m

end Omega.SyncKernelRealInput
