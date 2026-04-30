import Mathlib.Tactic
import Omega.Zeta.XiDirichletResidueFourierParsevalExact

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

abbrev conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue :=
  Omega.Zeta.xi_dirichlet_residue_fourier_parseval_exact_modulus

/-- Concrete finite residue table and the distinguished atomic residue trajectory. -/
structure conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data where
  conclusion_realinput40_residue_fourier_recovery_delta_trajectory_weight :
    conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue → ℂ
  conclusion_realinput40_residue_fourier_recovery_delta_trajectory_atom :
    conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue

/-- Delta mass on the packaged atomic residue. -/
def conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta
    (D : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data)
    (r : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue) : ℂ :=
  if r = D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_atom then 1 else 0

namespace conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data

/-- Finite Fourier inversion recovers the residue table from its two twisted traces. -/
def finiteFourierRecovery
    (D : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data) : Prop :=
  ∀ r : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue,
    D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_weight r =
      (1 / (2 : ℂ)) *
        ∑ j,
          Omega.Zeta.xi_dirichlet_residue_fourier_parseval_exact_trace
              D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_weight j *
            Omega.Zeta.xi_dirichlet_residue_fourier_parseval_exact_character j r

/-- The atomic component is supported exactly at the packaged residue. -/
def atomicDeltaSupport
    (D : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data) : Prop :=
  conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta D
      D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_atom = 1 ∧
    ∀ r : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_residue,
      r ≠ D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_atom →
        conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta D r = 0

end conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data

/-- Paper label: `thm:conclusion-realinput40-residue-fourier-recovery-delta-trajectory`. -/
theorem paper_conclusion_realinput40_residue_fourier_recovery_delta_trajectory
    (D : conclusion_realinput40_residue_fourier_recovery_delta_trajectory_data) :
    D.finiteFourierRecovery ∧ D.atomicDeltaSupport := by
  refine ⟨?_, ?_⟩
  · exact
      (Omega.Zeta.paper_xi_dirichlet_residue_fourier_parseval_exact
        D.conclusion_realinput40_residue_fourier_recovery_delta_trajectory_weight
        (conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta D)).1
  · constructor
    · simp [conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta]
    · intro r hr
      simp [conclusion_realinput40_residue_fourier_recovery_delta_trajectory_delta, hr]

end

end Omega.Conclusion
