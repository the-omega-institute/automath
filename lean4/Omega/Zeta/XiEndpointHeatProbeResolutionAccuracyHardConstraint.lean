import Mathlib

namespace Omega.Zeta

/-- Entrywise maximum norm on the finite Toeplitz blocks used in the hard-constraint estimate. -/
noncomputable def xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entrywiseNorm
    (N : ℕ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ℝ :=
  Finset.sup'
    ((Finset.univ : Finset (Fin (N + 1))).product (Finset.univ : Finset (Fin (N + 1))))
    (by simp)
    (fun ij => |A ij.1 ij.2|)

/-- The hard-constraint theorem only needs an explicit entrywise matrix norm on the finite
Toeplitz blocks. -/
noncomputable instance
    xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_instNormMatrix (N : ℕ) :
    Norm (Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) where
  norm := xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entrywiseNorm N

/-- Paper label: `thm:xi-endpoint-heat-probe-resolution-accuracy-hard-constraint`. The inherited
entrywise maximum norm on finite matrices is controlled by the entrywise error, hence a fortiori by
`(N + 1) * δ`. -/
theorem paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint
    (N : ℕ) (T That : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (δ : ℝ)
    (hentry : ∀ i j, |That i j - T i j| ≤ δ) :
    ‖That - T‖ ≤ (N + 1 : ℝ) * δ := by
  classical
  let paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entries :
      Finset (Fin (N + 1) × Fin (N + 1)) :=
    (Finset.univ : Finset (Fin (N + 1))).product (Finset.univ : Finset (Fin (N + 1)))
  have hδ_nonneg : 0 ≤ δ := by
    have h00 := hentry 0 0
    linarith [abs_nonneg (That 0 0 - T 0 0)]
  have hnorm_le_delta : ‖That - T‖ ≤ δ := by
    change
      xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entrywiseNorm N (That - T) ≤ δ
    unfold xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entrywiseNorm
    change
      Finset.sup' paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entries
          (by simp [paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entries])
          (fun ij : Fin (N + 1) × Fin (N + 1) => |(That - T) ij.1 ij.2|) ≤
        δ
    refine
      Finset.sup'_le
        (s := paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entries)
        (f := fun ij : Fin (N + 1) × Fin (N + 1) => |(That - T) ij.1 ij.2|)
        (H := by simp [paper_xi_endpoint_heat_probe_resolution_accuracy_hard_constraint_entries]) ?_
    intro ij hij
    simpa [Matrix.sub_apply, abs_sub_comm] using hentry ij.1 ij.2
  calc
    ‖That - T‖ ≤ δ := hnorm_le_delta
    _ ≤ (N + 1 : ℝ) * δ := by
      nlinarith [hδ_nonneg, show (1 : ℝ) ≤ N + 1 by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)]

end Omega.Zeta
