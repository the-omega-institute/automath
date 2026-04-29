import Mathlib

namespace Omega.CircleDimension

/-- Concrete spacing data for the logistic boundary-tail inversion. -/
structure xi_logistic_boundary_mass_inverts_spacing_Data where
  m : Nat
  Delta : Fin m → ℝ
  hDelta_pos : ∀ j, 0 < Delta j

/-- One-sided logistic tail mass at half-spacing. -/
noncomputable def xi_logistic_boundary_mass_inverts_spacing_tail
    (D : xi_logistic_boundary_mass_inverts_spacing_Data) (j : Fin D.m) : ℝ :=
  (1 + Real.exp (D.Delta j / 2))⁻¹

/-- Average multiclass boundary error as a linear sum of one-sided boundary masses. -/
noncomputable def xi_logistic_boundary_mass_inverts_spacing_average_error
    (D : xi_logistic_boundary_mass_inverts_spacing_Data) : ℝ :=
  (2 / (D.m + 1 : ℝ)) *
    ∑ j : Fin D.m, xi_logistic_boundary_mass_inverts_spacing_tail D j

/-- Concrete claim: each logistic boundary mass lies in `(0, 1/2)`, inverts to the spacing,
and the average error is the advertised linear boundary-mass summary. -/
def xi_logistic_boundary_mass_inverts_spacing_Data.xi_logistic_boundary_mass_inverts_spacing_claim
    (D : xi_logistic_boundary_mass_inverts_spacing_Data) : Prop :=
  (∀ j : Fin D.m,
      let e := xi_logistic_boundary_mass_inverts_spacing_tail D j
      0 < e ∧ e < (1 : ℝ) / 2 ∧
        D.Delta j = 2 * Real.log ((1 - e) / e)) ∧
    xi_logistic_boundary_mass_inverts_spacing_average_error D =
      (2 / (D.m + 1 : ℝ)) *
        ∑ j : Fin D.m, xi_logistic_boundary_mass_inverts_spacing_tail D j

lemma xi_logistic_boundary_mass_inverts_spacing_tail_inverse
    {x e : ℝ} (hx : 0 < x) (he : e = (1 + Real.exp (x / 2))⁻¹) :
    0 < e ∧ e < (1 : ℝ) / 2 ∧ x = 2 * Real.log ((1 - e) / e) := by
  subst e
  set t : ℝ := Real.exp (x / 2)
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hx_half : 0 < x / 2 := by linarith
  have ht_gt_one : 1 < t := by
    dsimp [t]
    exact Real.one_lt_exp_iff.mpr hx_half
  have hden_pos : 0 < 1 + t := by linarith
  have htail_pos : 0 < (1 + t)⁻¹ := inv_pos.mpr hden_pos
  refine ⟨htail_pos, ?_, ?_⟩
  · have hlt : (1 + t)⁻¹ < (2 : ℝ)⁻¹ := by
      rw [inv_lt_inv₀ hden_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    simpa [one_div] using hlt
  · have hratio : (1 - (1 + t)⁻¹) / (1 + t)⁻¹ = t := by
      field_simp [hden_pos.ne']
      ring
    calc
      x = 2 * (x / 2) := by ring
      _ = 2 * Real.log t := by
        simp [t]
      _ = 2 * Real.log ((1 - (1 + t)⁻¹) / (1 + t)⁻¹) := by
        rw [hratio]

/-- Paper label: `cor:xi-logistic-boundary-mass-inverts-spacing`. -/
theorem paper_xi_logistic_boundary_mass_inverts_spacing
    (D : xi_logistic_boundary_mass_inverts_spacing_Data) :
    D.xi_logistic_boundary_mass_inverts_spacing_claim := by
  refine ⟨?_, rfl⟩
  intro j
  exact xi_logistic_boundary_mass_inverts_spacing_tail_inverse (D.hDelta_pos j) rfl

end Omega.CircleDimension
