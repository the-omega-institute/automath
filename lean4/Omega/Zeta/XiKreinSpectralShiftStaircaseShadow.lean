import Omega.Zeta.XiKreinSpectralShiftEqualsKL

namespace Omega.Zeta

noncomputable section

/-- Paper label: `prop:xi-krein-spectral-shift-staircase-shadow`. -/
theorem paper_xi_krein_spectral_shift_staircase_shadow
    (a b t : ℝ) (ht : 0 < t) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let R := (t + a) / (t + b)
    let Pα : Fin 1 → ℝ := fun _ => 1
    let Pβ : Fin 1 → ℝ := fun _ => (t + b) / (t + a)
    let ξ : Fin 1 → ℝ := fun _ => Real.log (1 / ((t + b) / (t + a)))
    0 < R ∧
      xi_krein_spectral_shift_equals_kl_kl_divergence Pα Pβ =
        xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral ξ ∧
      xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral ξ = Real.log R := by
  dsimp
  have hta : 0 < t + a := by linarith
  have htb : 0 < t + b := by linarith
  have hratio : 1 / ((t + b) / (t + a)) = (t + a) / (t + b) := by
    field_simp [hta.ne', htb.ne']
  have hVisible :
      xi_krein_spectral_shift_equals_kl_visible_sigma_identification
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => (t + b) / (t + a))
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => (t + b) / (t + a)) := by
    rfl
  have hKrein :
      xi_krein_spectral_shift_equals_kl_krein_formula
        (fun _ : Fin 1 => 1) (fun _ : Fin 1 => (t + b) / (t + a))
        (fun _ : Fin 1 => Real.log (1 / ((t + b) / (t + a)))) := by
    simp [xi_krein_spectral_shift_equals_kl_krein_formula,
      xi_krein_spectral_shift_equals_kl_rn_entropy_integral,
      xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral]
  refine ⟨div_pos hta htb, ?_, ?_⟩
  · simpa using
      (paper_xi_krein_spectral_shift_equals_kl
        (Pα := fun _ : Fin 1 => 1)
        (Pβ := fun _ : Fin 1 => (t + b) / (t + a))
        (σα := fun _ : Fin 1 => 1)
        (σβ := fun _ : Fin 1 => (t + b) / (t + a))
        (ξ := fun _ : Fin 1 => Real.log (1 / ((t + b) / (t + a))))
        hVisible hKrein)
  · simp [xi_krein_spectral_shift_equals_kl_spectral_shift_density_integral, hratio]

end

end Omega.Zeta
