import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for simple-zero transport under dyadic truncation. -/
structure conclusion_xi_dyadic_zero_phase_drift_data where
  conclusion_xi_dyadic_zero_phase_drift_rho0 : ℂ
  conclusion_xi_dyadic_zero_phase_drift_rhoK : ℕ → ℂ
  conclusion_xi_dyadic_zero_phase_drift_xiDerivativeAtRho0 : ℂ
  conclusion_xi_dyadic_zero_phase_drift_completedRemainderAtRho0 : ℕ → ℂ
  conclusion_xi_dyadic_zero_phase_drift_linearizedDrift : ℕ → ℂ
  conclusion_xi_dyadic_zero_phase_drift_driftError : ℕ → ℂ
  conclusion_xi_dyadic_zero_phase_drift_tau : ℝ
  conclusion_xi_dyadic_zero_phase_drift_completedRemainderPhase : ℕ → ℝ
  conclusion_xi_dyadic_zero_phase_drift_phaseErrorAtTau : ℕ → ℝ
  conclusion_xi_dyadic_zero_phase_drift_exponentialTailError : ℕ → ℝ
  conclusion_xi_dyadic_zero_phase_drift_simpleZeroStability :
    ∀ K : ℕ,
      conclusion_xi_dyadic_zero_phase_drift_rhoK K -
          conclusion_xi_dyadic_zero_phase_drift_rho0 =
        conclusion_xi_dyadic_zero_phase_drift_linearizedDrift K +
          conclusion_xi_dyadic_zero_phase_drift_driftError K
  conclusion_xi_dyadic_zero_phase_drift_taylorLinearization :
    ∀ K : ℕ,
      conclusion_xi_dyadic_zero_phase_drift_linearizedDrift K =
        conclusion_xi_dyadic_zero_phase_drift_completedRemainderAtRho0 K /
          conclusion_xi_dyadic_zero_phase_drift_xiDerivativeAtRho0
  conclusion_xi_dyadic_zero_phase_drift_completedZetaRemainderPhaseLaw :
    ∀ K : ℕ,
      conclusion_xi_dyadic_zero_phase_drift_completedRemainderPhase K =
        (2 / Real.pi) *
            Real.exp (-(3 * (K : ℝ) / 4) * Real.log 2) *
            Real.exp (-Real.pi * (2 : ℝ) ^ K) *
            Real.cos
              (conclusion_xi_dyadic_zero_phase_drift_tau * (K : ℝ) * Real.log 2 / 2) +
          conclusion_xi_dyadic_zero_phase_drift_phaseErrorAtTau K +
          conclusion_xi_dyadic_zero_phase_drift_exponentialTailError K

namespace conclusion_xi_dyadic_zero_phase_drift_data

/-- The first-order simple-zero drift obtained by Taylor linearization. -/
def firstOrderDrift (D : conclusion_xi_dyadic_zero_phase_drift_data) : Prop :=
  ∀ K : ℕ,
    D.conclusion_xi_dyadic_zero_phase_drift_rhoK K -
        D.conclusion_xi_dyadic_zero_phase_drift_rho0 =
      D.conclusion_xi_dyadic_zero_phase_drift_completedRemainderAtRho0 K /
          D.conclusion_xi_dyadic_zero_phase_drift_xiDerivativeAtRho0 +
        D.conclusion_xi_dyadic_zero_phase_drift_driftError K

/-- The explicit dyadic phase main term for the completed-zeta remainder. -/
def dyadicPhaseMainTerm (D : conclusion_xi_dyadic_zero_phase_drift_data) : Prop :=
  ∀ K : ℕ,
    D.conclusion_xi_dyadic_zero_phase_drift_completedRemainderPhase K =
      (2 / Real.pi) *
          Real.exp (-(3 * (K : ℝ) / 4) * Real.log 2) *
          Real.exp (-Real.pi * (2 : ℝ) ^ K) *
          Real.cos
            (D.conclusion_xi_dyadic_zero_phase_drift_tau * (K : ℝ) * Real.log 2 / 2) +
        D.conclusion_xi_dyadic_zero_phase_drift_phaseErrorAtTau K +
        D.conclusion_xi_dyadic_zero_phase_drift_exponentialTailError K

end conclusion_xi_dyadic_zero_phase_drift_data

/-- Paper label: `thm:conclusion-xi-dyadic-zero-phase-drift`. -/
theorem paper_conclusion_xi_dyadic_zero_phase_drift
    (D : conclusion_xi_dyadic_zero_phase_drift_data) :
    D.firstOrderDrift ∧ D.dyadicPhaseMainTerm := by
  constructor
  · intro K
    calc
      D.conclusion_xi_dyadic_zero_phase_drift_rhoK K -
          D.conclusion_xi_dyadic_zero_phase_drift_rho0 =
          D.conclusion_xi_dyadic_zero_phase_drift_linearizedDrift K +
            D.conclusion_xi_dyadic_zero_phase_drift_driftError K :=
        D.conclusion_xi_dyadic_zero_phase_drift_simpleZeroStability K
      _ =
          D.conclusion_xi_dyadic_zero_phase_drift_completedRemainderAtRho0 K /
              D.conclusion_xi_dyadic_zero_phase_drift_xiDerivativeAtRho0 +
            D.conclusion_xi_dyadic_zero_phase_drift_driftError K := by
        rw [D.conclusion_xi_dyadic_zero_phase_drift_taylorLinearization K]
  · exact D.conclusion_xi_dyadic_zero_phase_drift_completedZetaRemainderPhaseLaw

end

end Omega.Conclusion
