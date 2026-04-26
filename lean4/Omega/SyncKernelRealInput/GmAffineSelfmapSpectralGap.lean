import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF

namespace Omega.SyncKernelRealInput

open Matrix

/-- The affine-consistency fixed-point count inherited from the compiled one-state constraint
presentation. -/
def gm_affine_selfmap_spectral_gap_fixCount (m : ℕ) : ℕ :=
  gm_sofic_zeck_linear_constraints_pf_omega_count m

/-- The compiled affine-consistency transition matrix. -/
def gm_affine_selfmap_spectral_gap_matrix :
    Matrix gm_sofic_zeck_linear_constraints_pf_state
      gm_sofic_zeck_linear_constraints_pf_state ℕ :=
  gm_sofic_zeck_linear_constraints_pf_transition_matrix

/-- The entry vector for the affine-consistency presentation. -/
def gm_affine_selfmap_spectral_gap_entryVector :
    gm_sofic_zeck_linear_constraints_pf_state → ℕ :=
  gm_sofic_zeck_linear_constraints_pf_entry_vector

/-- The exit vector for the affine-consistency presentation. -/
def gm_affine_selfmap_spectral_gap_exitVector :
    gm_sofic_zeck_linear_constraints_pf_state → ℕ :=
  gm_sofic_zeck_linear_constraints_pf_exit_vector

/-- The Perron root of the affine-consistency matrix. -/
def gm_affine_selfmap_spectral_gap_rho : ℝ :=
  gm_sofic_zeck_linear_constraints_pf_perron_root

/-- Paper label: `thm:gm-affine-selfmap-spectral-gap`.
The compiled linear-constraint presentation provides the matrix-power formula for the affine
consistency count, and in the chapter-local one-state model the Perron root is `1`, so every
ambient entropy level `α > 1` leaves a positive gap `ε = α - 1`. -/
theorem paper_gm_affine_selfmap_spectral_gap (α : ℝ) (hα : 1 < α) :
    (∀ m : ℕ,
      gm_affine_selfmap_spectral_gap_fixCount m =
        gm_affine_selfmap_spectral_gap_entryVector 0 *
          (gm_affine_selfmap_spectral_gap_matrix ^ m) 0 0 *
            gm_affine_selfmap_spectral_gap_exitVector 0) ∧
      gm_affine_selfmap_spectral_gap_rho < α ∧
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ m : ℕ, (gm_affine_selfmap_spectral_gap_fixCount m : ℝ) ≤ (α - ε) ^ m := by
  rcases paper_gm_sofic_zeck_linear_constraints_pf with ⟨_, _, _, hcount, _, hgrowth⟩
  have hrho : gm_affine_selfmap_spectral_gap_rho = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro m
    simpa [gm_affine_selfmap_spectral_gap_fixCount, gm_affine_selfmap_spectral_gap_entryVector,
      gm_affine_selfmap_spectral_gap_matrix, gm_affine_selfmap_spectral_gap_exitVector] using
      hcount m
  · simpa [hrho] using hα
  · refine ⟨α - gm_affine_selfmap_spectral_gap_rho, ?_, ?_⟩
    · exact sub_pos.mpr (by simpa [hrho] using hα)
    · intro m
      have hbase : α - (α - gm_affine_selfmap_spectral_gap_rho) = 1 := by
        simp [hrho]
      have hfix : (gm_affine_selfmap_spectral_gap_fixCount m : ℝ) = 1 := by
        have hreal := hgrowth m
        calc
          (gm_affine_selfmap_spectral_gap_fixCount m : ℝ)
              = gm_affine_selfmap_spectral_gap_rho ^ m := by
                  simpa [gm_affine_selfmap_spectral_gap_fixCount,
                    gm_affine_selfmap_spectral_gap_rho] using hreal
          _ = 1 := by simp [hrho]
      rw [hfix, hbase]
      simp only [one_pow, le_refl]

end Omega.SyncKernelRealInput
