import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65e-rouche-boundary-margin-rh-certificate`. -/
theorem paper_xi_time_part65e_rouche_boundary_margin_rh_certificate
    (rho : ℕ → ℝ)
    (FzetaZeroFreeOnClosedDisk : ℝ → Prop)
    (RoucheMarginCertificate : ℕ → Prop)
    (RH : Prop)
    (hrho_exhausts : ∀ r : ℝ, 0 < r → r < 1 → ∃ N : ℕ, r ≤ rho N)
    (hrouche :
      ∀ N : ℕ, RoucheMarginCertificate N → FzetaZeroFreeOnClosedDisk (rho N))
    (hcertificate : ∀ N : ℕ, RoucheMarginCertificate N)
    (hmono :
      ∀ {r R : ℝ}, 0 < r → r ≤ R →
        FzetaZeroFreeOnClosedDisk R → FzetaZeroFreeOnClosedDisk r)
    (hRH : (∀ r : ℝ, 0 < r → r < 1 → FzetaZeroFreeOnClosedDisk r) → RH) :
    RH := by
  apply hRH
  intro r hr_pos hr_lt
  rcases hrho_exhausts r hr_pos hr_lt with ⟨N, hr_le⟩
  exact hmono hr_pos hr_le (hrouche N (hcertificate N))

end Omega.Zeta
