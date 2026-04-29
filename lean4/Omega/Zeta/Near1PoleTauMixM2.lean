import Omega.Zeta.Near1PoleDiffusiveSp

namespace Omega.Zeta

/-- Paper label: `cor:near1-pole-taumix-m2`. -/
theorem paper_near1_pole_taumix_m2
    (lam : ℝ) (rho tauMix Gamma : ℕ → ℝ) (hm2Asymptotic : Prop)
    (hlam : 1 < lam)
    (htau : ∀ m, 2 ≤ m → tauMix m = 1 / (-Real.log (rho m / lam)))
    (hGamma : ∀ m, 2 ≤ m → Gamma m = -Real.log (rho m / lam) / Real.log lam)
    (hlog : ∀ m, 2 ≤ m → -Real.log (rho m / lam) ≠ 0) (hm2 : hm2Asymptotic) :
    (∀ m, 2 ≤ m → Gamma m * tauMix m = 1 / Real.log lam) ∧ hm2Asymptotic := by
  refine ⟨?_, hm2⟩
  intro m hm
  rw [hGamma m hm, htau m hm]
  have hlogLam_ne : Real.log lam ≠ 0 := (Real.log_pos hlam).ne'
  have hspectral_ne : -Real.log (rho m / lam) ≠ 0 := hlog m hm
  have hraw_ne : Real.log (rho m / lam) ≠ 0 := by
    intro hraw
    exact hspectral_ne (by simp [hraw])
  field_simp [hlogLam_ne, hspectral_ne, hraw_ne]

end Omega.Zeta
