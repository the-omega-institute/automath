import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper-facing asymptotic obstruction: a zero-counting statistic tending to zero cannot control a
collision gap with positive eventual floor by any modulus of continuity plus a vanishing error. -/
def xi_time_part75a_zero_counting_insufficient_for_uniformity_gap_statement : Prop :=
  ∀ (zeroDensity collisionGap error : ℕ → ℝ) (c : ℝ),
    (∀ m, 0 ≤ zeroDensity m) →
      (∀ r : ℝ, 0 < r → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → zeroDensity m < r) →
        (∀ r : ℝ, 0 < r → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → error m < r) →
          0 < c →
            (∃ M : ℕ, ∀ m : ℕ, M ≤ m → c ≤ collisionGap m) →
              ¬ ∃ omega : ℝ → ℝ,
                (∀ r : ℝ, 0 < r → ∃ rho : ℝ, 0 < rho ∧
                  ∀ t : ℝ, 0 ≤ t → t < rho → omega t < r) ∧
                  ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
                    collisionGap m ≤ omega (zeroDensity m) + error m

/-- Paper label: `thm:xi-time-part75a-zero-counting-insufficient-for-uniformity-gap`. -/
theorem paper_xi_time_part75a_zero_counting_insufficient_for_uniformity_gap :
    xi_time_part75a_zero_counting_insufficient_for_uniformity_gap_statement := by
  intro zeroDensity collisionGap error c hzero_nonneg hzero_vanish herror_vanish hc hgap
  rintro ⟨omega, homega, hcontrol⟩
  have hc_half : 0 < c / 2 := by linarith
  rcases homega (c / 2) hc_half with ⟨rho, hrho_pos, homega_rho⟩
  rcases hzero_vanish rho hrho_pos with ⟨Mzero, hzero_small⟩
  rcases herror_vanish (c / 2) hc_half with ⟨Merror, herror_small⟩
  rcases hgap with ⟨Mgap, hgap_floor⟩
  rcases hcontrol with ⟨Mcontrol, hcontrol_bound⟩
  let m := max Mzero (max Merror (max Mgap Mcontrol))
  have hm_zero : Mzero ≤ m := by
    dsimp [m]
    omega
  have hm_error : Merror ≤ m := by
    dsimp [m]
    omega
  have hm_gap : Mgap ≤ m := by
    dsimp [m]
    omega
  have hm_control : Mcontrol ≤ m := by
    dsimp [m]
    omega
  have hmod_small : omega (zeroDensity m) < c / 2 :=
    homega_rho (zeroDensity m) (hzero_nonneg m) (hzero_small m hm_zero)
  have herr_small : error m < c / 2 :=
    herror_small m hm_error
  have hupper : collisionGap m < c := by
    have hcontrol_m := hcontrol_bound m hm_control
    linarith
  have hlower : c ≤ collisionGap m := hgap_floor m hm_gap
  linarith

end Omega.Zeta
