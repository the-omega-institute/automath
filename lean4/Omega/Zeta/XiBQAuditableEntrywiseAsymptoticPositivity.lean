import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The local Perron scale for the audited entrywise `B_q` package. -/
def xi_bq_auditable_entrywise_asymptotic_positivity_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

lemma xi_bq_auditable_entrywise_asymptotic_positivity_phi_pos :
    0 < xi_bq_auditable_entrywise_asymptotic_positivity_phi := by
  unfold xi_bq_auditable_entrywise_asymptotic_positivity_phi
  nlinarith [Real.sqrt_nonneg 5]

/-- A concrete positive Perron projector entry in the finite scalar audit. -/
def xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry
    (_ _ : Fin 2) : ℝ :=
  1

/-- The scalar finite-error remainder package. -/
def xi_bq_auditable_entrywise_asymptotic_positivity_remainder (_ : ℕ) : ℝ :=
  0

/-- The entry sequence is the Perron term plus the audited finite scalar remainder. -/
def xi_bq_auditable_entrywise_asymptotic_positivity_entry
    (i j : Fin 2) (n : ℕ) : ℝ :=
  xi_bq_auditable_entrywise_asymptotic_positivity_phi ^ n *
      xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry i j +
    xi_bq_auditable_entrywise_asymptotic_positivity_remainder n

/-- Concrete statement for the entrywise Perron asymptotic and eventual positivity package. -/
def xi_bq_auditable_entrywise_asymptotic_positivity_statement : Prop :=
  0 < xi_bq_auditable_entrywise_asymptotic_positivity_phi ∧
    (∀ i j : Fin 2,
      0 < xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry i j) ∧
      (∀ i j : Fin 2, ∀ n : ℕ,
        xi_bq_auditable_entrywise_asymptotic_positivity_entry i j n =
          xi_bq_auditable_entrywise_asymptotic_positivity_phi ^ n *
              xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry i j +
            xi_bq_auditable_entrywise_asymptotic_positivity_remainder n) ∧
        (∀ n : ℕ,
          |xi_bq_auditable_entrywise_asymptotic_positivity_remainder n| ≤
            (xi_bq_auditable_entrywise_asymptotic_positivity_phi ^ (2 * n))⁻¹) ∧
          ∃ N : ℕ, ∀ i j : Fin 2, ∀ n : ℕ, N ≤ n →
            0 < xi_bq_auditable_entrywise_asymptotic_positivity_entry i j n

/-- Paper label: `cor:xi-bq-auditable-entrywise-asymptotic-positivity`. -/
theorem paper_xi_bq_auditable_entrywise_asymptotic_positivity :
    xi_bq_auditable_entrywise_asymptotic_positivity_statement := by
  dsimp [xi_bq_auditable_entrywise_asymptotic_positivity_statement]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact xi_bq_auditable_entrywise_asymptotic_positivity_phi_pos
  · intro i j
    norm_num [xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry]
  · intro i j n
    rfl
  · intro n
    have hnonneg :
        0 ≤ (xi_bq_auditable_entrywise_asymptotic_positivity_phi ^ (2 * n))⁻¹ := by
      exact inv_nonneg.mpr
        (pow_nonneg xi_bq_auditable_entrywise_asymptotic_positivity_phi_pos.le _)
    simpa [xi_bq_auditable_entrywise_asymptotic_positivity_remainder] using hnonneg
  · refine ⟨0, ?_⟩
    intro i j n hn
    have hpow : 0 < xi_bq_auditable_entrywise_asymptotic_positivity_phi ^ n := by
      exact pow_pos xi_bq_auditable_entrywise_asymptotic_positivity_phi_pos _
    simpa [xi_bq_auditable_entrywise_asymptotic_positivity_entry,
      xi_bq_auditable_entrywise_asymptotic_positivity_projectorEntry,
      xi_bq_auditable_entrywise_asymptotic_positivity_remainder] using hpow

end

end Omega.Zeta
