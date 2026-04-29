import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.KernelHardyRealEven

namespace Omega.UnitCirclePhaseArithmetic

open Omega.SyncKernelWeighted

/-- The odd Cayley time parameter used to compactify the critical line by inversion. -/
noncomputable def xi_nonperiodic_phase_symmetry_cayley_time (u : ℝˣ) : ℝ :=
  ((u : ℝ) - (u : ℝ)⁻¹) / 2

/-- The compactified critical-line section of the concrete `Ξ` proxy. -/
noncomputable def xi_nonperiodic_phase_symmetry_compactified_xi (u : ℝˣ) : ℂ :=
  kernelHardyZ (xi_nonperiodic_phase_symmetry_cayley_time u)

/-- Real-valuedness plus inversion symmetry for the compactified critical-line section. -/
def xi_nonperiodic_phase_symmetry_statement : Prop :=
  ∀ u : ℝˣ,
    (∃ r : ℝ, xi_nonperiodic_phase_symmetry_compactified_xi u = r) ∧
      xi_nonperiodic_phase_symmetry_compactified_xi u⁻¹ =
        xi_nonperiodic_phase_symmetry_compactified_xi u

lemma xi_nonperiodic_phase_symmetry_cayley_time_inv (u : ℝˣ) :
    xi_nonperiodic_phase_symmetry_cayley_time u⁻¹ =
      -xi_nonperiodic_phase_symmetry_cayley_time u := by
  have hu : (u : ℝ) ≠ 0 := Units.ne_zero u
  unfold xi_nonperiodic_phase_symmetry_cayley_time
  simp
  ring

/-- Paper label: `prop:xi-nonperiodic-phase-symmetry`.
Passing to the odd Cayley time parameter preserves the critical-line real-valuedness of the
concrete `Ξ` proxy, and the evenness of the Hardy section upgrades the functional equation to the
inversion law `u ↦ 1 / u`. -/
theorem paper_xi_nonperiodic_phase_symmetry : xi_nonperiodic_phase_symmetry_statement := by
  rcases paper_kernel_hardy_real_even with ⟨hreal, heven, _⟩
  intro u
  refine ⟨hreal (xi_nonperiodic_phase_symmetry_cayley_time u), ?_⟩
  change kernelHardyZ (xi_nonperiodic_phase_symmetry_cayley_time u⁻¹) =
    kernelHardyZ (xi_nonperiodic_phase_symmetry_cayley_time u)
  rw [xi_nonperiodic_phase_symmetry_cayley_time_inv]
  simpa using heven (xi_nonperiodic_phase_symmetry_cayley_time u)

end Omega.UnitCirclePhaseArithmetic
