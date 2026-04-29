import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete jet data for the xi Caratheodory--Toeplitz PSD equivalence.  The real jet
coefficients, the horizon Caratheodory moments, and the finite Toeplitz principal witnesses are
recorded as sequences; the two audit fields are the coefficient-localization and horizon LMI
equivalences used by the paper statement. -/
structure xi_jet_psd_equivalence_data where
  xi_jet_psd_equivalence_jet : ℕ → ℝ
  xi_jet_psd_equivalence_caratheodoryMoment : ℕ → ℝ
  xi_jet_psd_equivalence_toeplitzPrincipalMinor : ℕ → ℝ
  xi_jet_psd_equivalence_coefficientLocalization :
    (∀ k : ℕ, xi_jet_psd_equivalence_jet k = 0) ↔
      ∀ N : ℕ, 0 ≤ xi_jet_psd_equivalence_caratheodoryMoment N
  xi_jet_psd_equivalence_horizonToeplitzLMI :
    ∀ N : ℕ,
      0 ≤ xi_jet_psd_equivalence_caratheodoryMoment N ↔
        0 ≤ xi_jet_psd_equivalence_toeplitzPrincipalMinor N

/-- The jet-local RH predicate: all recorded off-critical jet defects vanish. -/
def xi_jet_psd_equivalence_rh (D : xi_jet_psd_equivalence_data) : Prop :=
  ∀ k : ℕ, D.xi_jet_psd_equivalence_jet k = 0

/-- Caratheodory positivity at every finite horizon. -/
def xi_jet_psd_equivalence_caratheodory_positive
    (D : xi_jet_psd_equivalence_data) : Prop :=
  ∀ N : ℕ, 0 ≤ D.xi_jet_psd_equivalence_caratheodoryMoment N

/-- The finite Toeplitz PSD predicate at one horizon, represented by the audited principal
minor used as the finite failure projection. -/
def xi_jet_psd_equivalence_horizon_toeplitz_psd
    (D : xi_jet_psd_equivalence_data) (N : ℕ) : Prop :=
  0 ≤ D.xi_jet_psd_equivalence_toeplitzPrincipalMinor N

/-- Toeplitz PSD at every finite horizon. -/
def xi_jet_psd_equivalence_all_level_toeplitz_psd
    (D : xi_jet_psd_equivalence_data) : Prop :=
  ∀ N : ℕ, xi_jet_psd_equivalence_horizon_toeplitz_psd D N

/-- A projected finite PSD failure witness. -/
def xi_jet_psd_equivalence_finite_psd_failure
    (D : xi_jet_psd_equivalence_data) (N : ℕ) : Prop :=
  D.xi_jet_psd_equivalence_toeplitzPrincipalMinor N < 0

/-- Paper-facing statement: RH, Caratheodory positivity, and the all-level Toeplitz PSD tower are
equivalent, and failure of the tower projects to a finite negative principal witness. -/
def xi_jet_psd_equivalence_statement (D : xi_jet_psd_equivalence_data) : Prop :=
  (xi_jet_psd_equivalence_rh D ↔ xi_jet_psd_equivalence_caratheodory_positive D) ∧
    (xi_jet_psd_equivalence_caratheodory_positive D ↔
      xi_jet_psd_equivalence_all_level_toeplitz_psd D) ∧
      (xi_jet_psd_equivalence_rh D ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd D) ∧
        (¬ xi_jet_psd_equivalence_all_level_toeplitz_psd D →
          ∃ N : ℕ, xi_jet_psd_equivalence_finite_psd_failure D N)

/-- Paper label: `thm:xi-jet-psd-equivalence`. -/
theorem paper_xi_jet_psd_equivalence
    (D : xi_jet_psd_equivalence_data) : xi_jet_psd_equivalence_statement D := by
  classical
  have hRHCarath :
      xi_jet_psd_equivalence_rh D ↔ xi_jet_psd_equivalence_caratheodory_positive D := by
    simpa [xi_jet_psd_equivalence_rh, xi_jet_psd_equivalence_caratheodory_positive] using
      D.xi_jet_psd_equivalence_coefficientLocalization
  have hCarathToeplitz :
      xi_jet_psd_equivalence_caratheodory_positive D ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd D := by
    constructor
    · intro hcarath N
      exact (D.xi_jet_psd_equivalence_horizonToeplitzLMI N).mp (hcarath N)
    · intro htoeplitz N
      exact (D.xi_jet_psd_equivalence_horizonToeplitzLMI N).mpr (htoeplitz N)
  have hRHToeplitz :
      xi_jet_psd_equivalence_rh D ↔
        xi_jet_psd_equivalence_all_level_toeplitz_psd D :=
    hRHCarath.trans hCarathToeplitz
  refine ⟨hRHCarath, hCarathToeplitz, hRHToeplitz, ?_⟩
  intro hnot
  rw [xi_jet_psd_equivalence_all_level_toeplitz_psd] at hnot
  push_neg at hnot
  rcases hnot with ⟨N, hN⟩
  have hN' : ¬ 0 ≤ D.xi_jet_psd_equivalence_toeplitzPrincipalMinor N := by
    simpa [xi_jet_psd_equivalence_horizon_toeplitz_psd] using hN
  exact ⟨N, lt_of_not_ge hN'⟩

end Omega.Zeta
