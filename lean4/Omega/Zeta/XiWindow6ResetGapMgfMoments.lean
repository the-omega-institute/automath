import Mathlib.Tactic

namespace Omega.Zeta

/-- prop:xi-window6-reset-gap-mgf-moments -/
theorem paper_xi_window6_reset_gap_mgf_moments (phi : ℝ) (hphi : phi ^ 2 = phi + 1)
    (hprob : 1 / phi + 1 / phi ^ 2 = 1) :
    let mean : ℝ := 55 / phi + 34 / phi ^ 2
    mean = 13 + 21 * phi ∧
      (55 - mean) ^ 2 / phi + (34 - mean) ^ 2 / phi ^ 2 = 441 * (2 * phi - 3) := by
  have hphi_ne : phi ≠ 0 := by
    intro h
    subst phi
    norm_num at hprob
  have hphi_sq_ne : phi ^ 2 ≠ 0 := pow_ne_zero 2 hphi_ne
  have h_inv : 1 / phi = phi - 1 := by
    field_simp [hphi_ne]
    nlinarith [hphi]
  have h_inv_sq : 1 / phi ^ 2 = 2 - phi := by
    field_simp [hphi_sq_ne]
    nlinarith [hphi]
  have h_inv' : phi⁻¹ = phi - 1 := by
    simpa [one_div] using h_inv
  have h_inv_sq' : (phi ^ 2)⁻¹ = 2 - phi := by
    simpa [one_div] using h_inv_sq
  let mean : ℝ := 55 / phi + 34 / phi ^ 2
  have hmean : mean = 13 + 21 * phi := by
    dsimp [mean]
    simp only [div_eq_mul_inv, h_inv', h_inv_sq']
    ring
  refine ⟨hmean, ?_⟩
  dsimp [mean]
  simp only [div_eq_mul_inv, h_inv', h_inv_sq']
  ring_nf
  nlinarith [hphi]

end Omega.Zeta
