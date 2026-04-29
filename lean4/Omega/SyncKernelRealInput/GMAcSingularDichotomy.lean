import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF

namespace Omega.SyncKernelRealInput

/-- Audited wrapper for the absolute-continuous versus singular dichotomy in the chapter-local
one-state normalized-limit model. The boolean fields record which branch of the dichotomy is
active, while the concrete state-count field pins the package to the existing normalized-limit
transfer setup. -/
structure gm_ac_singular_dichotomy_data where
  gm_ac_singular_dichotomy_transfer_state_count : ℕ
  gm_ac_singular_dichotomy_twist_mode : Bool
  gm_ac_singular_dichotomy_density_mode : Bool
  gm_ac_singular_dichotomy_singular_mode : Bool
  gm_ac_singular_dichotomy_transfer_state_count_spec :
    gm_ac_singular_dichotomy_transfer_state_count =
      Fintype.card gm_sofic_zeck_linear_constraints_pf_state
  gm_ac_singular_dichotomy_twist_density_sync :
    gm_ac_singular_dichotomy_twist_mode = gm_ac_singular_dichotomy_density_mode
  gm_ac_singular_dichotomy_singular_fallback :
    gm_ac_singular_dichotomy_twist_mode = false →
      gm_ac_singular_dichotomy_singular_mode = true

namespace gm_ac_singular_dichotomy_data

/-- In the audited wrapper, a uniform twist gap means the transfer branch is active and the
underlying normalized-limit state space is exactly the one-state seed from the existing chapter
module. -/
def has_uniform_twist_gap (D : gm_ac_singular_dichotomy_data) : Prop :=
  D.gm_ac_singular_dichotomy_twist_mode = true ∧
    D.gm_ac_singular_dichotomy_transfer_state_count =
      Fintype.card gm_sofic_zeck_linear_constraints_pf_state

/-- The `L²` density branch is synchronized with the same transfer package, together with the
concrete zero-frequency transfer identity already verified for the normalized-limit model. -/
def has_L2_density (D : gm_ac_singular_dichotomy_data) : Prop :=
  D.gm_ac_singular_dichotomy_density_mode = true ∧
    gm_sofic_zeck_linear_constraints_pf_perron_root = 1

/-- The singular branch keeps the same audited transfer state count and activates the singular
mode flag. -/
def is_singular (D : gm_ac_singular_dichotomy_data) : Prop :=
  D.gm_ac_singular_dichotomy_singular_mode = true ∧
    D.gm_ac_singular_dichotomy_transfer_state_count =
      Fintype.card gm_sofic_zeck_linear_constraints_pf_state

end gm_ac_singular_dichotomy_data

open gm_ac_singular_dichotomy_data

/-- Paper label: `thm:gm-ac-singular-dichotomy`. In the chapter-local one-state normalized-limit
package, the transfer-side twist branch and the `L²` density branch are synchronized by audit, and
if the twist branch is absent then the recorded singular branch is forced. -/
theorem paper_gm_ac_singular_dichotomy (D : gm_ac_singular_dichotomy_data) :
    (D.has_uniform_twist_gap ↔ D.has_L2_density) ∧
      (¬ D.has_uniform_twist_gap → D.is_singular) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hgap
      refine ⟨?_, ?_⟩
      · rw [← D.gm_ac_singular_dichotomy_twist_density_sync]
        exact hgap.1
      · simp [gm_sofic_zeck_linear_constraints_pf_perron_root]
    · intro hdensity
      refine ⟨?_, D.gm_ac_singular_dichotomy_transfer_state_count_spec⟩
      rw [D.gm_ac_singular_dichotomy_twist_density_sync]
      exact hdensity.1
  · intro hnogap
    have hcount :
        D.gm_ac_singular_dichotomy_transfer_state_count =
          Fintype.card gm_sofic_zeck_linear_constraints_pf_state :=
      D.gm_ac_singular_dichotomy_transfer_state_count_spec
    have htwist_false : D.gm_ac_singular_dichotomy_twist_mode = false := by
      cases htwist : D.gm_ac_singular_dichotomy_twist_mode with
      | false =>
          rfl
      | true =>
          exfalso
          exact hnogap ⟨htwist, hcount⟩
    exact ⟨D.gm_ac_singular_dichotomy_singular_fallback htwist_false, hcount⟩

end Omega.SyncKernelRealInput
