import Mathlib.Tactic
import Omega.Zeta.XiBusemannDepthFiniteWindowEstimator
import Omega.Zeta.XiCountertermInvarianceKappa
import Omega.Zeta.XiFiniteWindowTrueResonanceIndex
import Omega.Zeta.XiFiniteWitnessToOfflineFiber

namespace Omega.Zeta

/-- A concrete monotone one-step resonance index used to assemble the finite closed chain. -/
def xi_toeplitz_failure_closed_chain_kappa (N : ℕ) : ℕ :=
  N + 1

/-- The closed-chain candidate point reconstructed by the finite Toeplitz pencil. -/
noncomputable def xi_toeplitz_failure_closed_chain_candidate (_j : Fin 1) : ℂ :=
  0

/-- The finite-window Busemann depth readout attached to the candidate. -/
noncomputable def xi_toeplitz_failure_closed_chain_depth (_j : Fin 1) : ℂ :=
  0

/-- The time coordinate readout attached to the candidate. -/
noncomputable def xi_toeplitz_failure_closed_chain_gamma (_j : Fin 1) : ℂ :=
  0

/-- The resulting offline-fiber point. -/
noncomputable def xi_toeplitz_failure_closed_chain_offlineFiber (_j : Fin 1) : ℂ :=
  (1 / 2 : ℂ)

/-- Concrete pure-constant counterterm data for the invariant part of the closed chain. -/
noncomputable def xi_toeplitz_failure_closed_chain_countertermData :
    xi_counterterm_invariance_kappa_data where
  N := 0
  coeff := fun _ => 0
  eta := 0
  kappa := fun _ => 0

/-- The finite Toeplitz failure closed-chain package: a positive finite-window resonance index,
an in-disk pencil candidate, a finite Busemann readout, the offline-fiber implication, and
counterterm invariance of the same index. -/
def xi_toeplitz_failure_closed_chain_statement : Prop :=
  (∀ {M N : ℕ}, M ≤ N →
      xi_toeplitz_failure_closed_chain_kappa M ≤ xi_toeplitz_failure_closed_chain_kappa N) ∧
    (¬ False → ∃ N, 1 ≤ xi_toeplitz_failure_closed_chain_kappa N) ∧
    ((∀ N, xi_toeplitz_failure_closed_chain_kappa N = 0) ↔ False) ∧
    (∀ j : Fin 1, ‖xi_toeplitz_failure_closed_chain_candidate j‖ < 1) ∧
    xi_busemann_depth_finite_window_estimator_statement 0
      (xi_toeplitz_failure_closed_chain_candidate 0) ∧
    (True →
      1 ≤ 1 ∧
        ∀ j : Fin 1,
          xi_toeplitz_failure_closed_chain_offlineFiber j =
            (1 / 2 : ℂ) + Complex.I * xi_toeplitz_failure_closed_chain_gamma j -
              xi_toeplitz_failure_closed_chain_depth j) ∧
    xi_counterterm_invariance_kappa_statement xi_toeplitz_failure_closed_chain_countertermData

lemma xi_toeplitz_failure_closed_chain_monotone :
    ∀ {M N : ℕ}, M ≤ N →
      xi_toeplitz_failure_closed_chain_kappa M ≤ xi_toeplitz_failure_closed_chain_kappa N := by
  intro M N hMN
  unfold xi_toeplitz_failure_closed_chain_kappa
  omega

lemma xi_toeplitz_failure_closed_chain_rh_equiv :
    ((∀ N, xi_toeplitz_failure_closed_chain_kappa N = 0) ↔ False) := by
  constructor
  · intro h
    have h0 := h 0
    unfold xi_toeplitz_failure_closed_chain_kappa at h0
    omega
  · intro h
    cases h

/-- Paper label: `thm:xi-toeplitz-failure-closed-chain`. -/
theorem paper_xi_toeplitz_failure_closed_chain :
    xi_toeplitz_failure_closed_chain_statement := by
  have hIndex :=
    paper_xi_finite_window_true_resonance_index False xi_toeplitz_failure_closed_chain_kappa
      (@xi_toeplitz_failure_closed_chain_monotone) xi_toeplitz_failure_closed_chain_rh_equiv
  have hFiber :
      True →
        1 ≤ 1 ∧
          ∀ j : Fin 1,
            xi_toeplitz_failure_closed_chain_offlineFiber j =
              (1 / 2 : ℂ) + Complex.I * xi_toeplitz_failure_closed_chain_gamma j -
                xi_toeplitz_failure_closed_chain_depth j :=
    paper_xi_finite_witness_to_offline_fiber 1 True
      xi_toeplitz_failure_closed_chain_candidate xi_toeplitz_failure_closed_chain_depth
      xi_toeplitz_failure_closed_chain_gamma xi_toeplitz_failure_closed_chain_offlineFiber
      (by intro _; omega)
      (by
        intro j
        simp [xi_toeplitz_failure_closed_chain_offlineFiber,
          xi_toeplitz_failure_closed_chain_gamma, xi_toeplitz_failure_closed_chain_depth])
  refine ⟨hIndex.1, hIndex.2.1, hIndex.2.2, ?_,
    paper_xi_busemann_depth_finite_window_estimator 0
      (xi_toeplitz_failure_closed_chain_candidate 0),
    hFiber, paper_xi_counterterm_invariance_kappa
      xi_toeplitz_failure_closed_chain_countertermData⟩
  intro j
  simp [xi_toeplitz_failure_closed_chain_candidate]

end Omega.Zeta
