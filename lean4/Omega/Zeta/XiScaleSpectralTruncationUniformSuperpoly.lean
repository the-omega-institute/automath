import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Zero ordinates retained by a height cutoff. -/
def xi_scale_spectral_truncation_uniform_superpoly_keptZeros
    (zeros : Finset ℤ) (Γ : ℕ) : Finset ℤ :=
  zeros.filter fun γ => Int.natAbs γ ≤ Γ

/-- Zero ordinates discarded by a height cutoff. -/
def xi_scale_spectral_truncation_uniform_superpoly_tailZeros
    (zeros : Finset ℤ) (Γ : ℕ) : Finset ℤ :=
  zeros.filter fun γ => Γ < Int.natAbs γ

/-- The finite spectral tail mass supplied by the analytic rapid-decay input. -/
def xi_scale_spectral_truncation_uniform_superpoly_tailMass
    (zeros : Finset ℤ) (weight : ℤ → ℝ) (Γ : ℕ) : ℝ :=
  (xi_scale_spectral_truncation_uniform_superpoly_tailZeros zeros Γ).sum weight

/-- Full coefficient expansion, written as retained modes plus discarded modes and a remainder. -/
def xi_scale_spectral_truncation_uniform_superpoly_fullCoeff
    (zeros : Finset ℤ) (term : ℕ → ℤ → ℂ) (remainder : ℕ → ℂ) (Γ m : ℕ) : ℂ :=
  -((xi_scale_spectral_truncation_uniform_superpoly_keptZeros zeros Γ).sum (term m) +
      (xi_scale_spectral_truncation_uniform_superpoly_tailZeros zeros Γ).sum (term m)) +
    remainder m

/-- Truncated coefficient expansion with the same remainder as the full coefficient. -/
def xi_scale_spectral_truncation_uniform_superpoly_truncatedCoeff
    (zeros : Finset ℤ) (term : ℕ → ℤ → ℂ) (remainder : ℕ → ℂ) (Γ m : ℕ) : ℂ :=
  -((xi_scale_spectral_truncation_uniform_superpoly_keptZeros zeros Γ).sum (term m)) +
    remainder m

/-- Concrete finite-tail form of the uniform super-polynomial truncation estimate. -/
def xi_scale_spectral_truncation_uniform_superpoly_statement : Prop :=
  ∀ (zeros : Finset ℤ) (weight : ℤ → ℝ) (term : ℕ → ℤ → ℂ) (remainder : ℕ → ℂ)
    (K : ℕ → ℝ),
    (∀ A Γ : ℕ, 2 ≤ Γ →
      xi_scale_spectral_truncation_uniform_superpoly_tailMass zeros weight Γ ≤
        K A / (Γ : ℝ) ^ A) →
    (∀ (m : ℕ) (γ : ℤ), γ ∈ zeros → ‖term m γ‖ ≤ weight γ) →
      ∀ A Γ : ℕ, 2 ≤ Γ →
        ∀ m : ℕ,
          ‖xi_scale_spectral_truncation_uniform_superpoly_fullCoeff
              zeros term remainder Γ m -
            xi_scale_spectral_truncation_uniform_superpoly_truncatedCoeff
              zeros term remainder Γ m‖ ≤
            K A / (Γ : ℝ) ^ A

/-- Paper label: `thm:xi-scale-spectral-truncation-uniform-superpoly`. -/
theorem paper_xi_scale_spectral_truncation_uniform_superpoly :
    xi_scale_spectral_truncation_uniform_superpoly_statement := by
  intro zeros weight term remainder K htail hterm A Γ hΓ m
  calc
    ‖xi_scale_spectral_truncation_uniform_superpoly_fullCoeff zeros term remainder Γ m -
        xi_scale_spectral_truncation_uniform_superpoly_truncatedCoeff
          zeros term remainder Γ m‖
        = ‖(xi_scale_spectral_truncation_uniform_superpoly_tailZeros zeros Γ).sum
            (term m)‖ := by
          simp [xi_scale_spectral_truncation_uniform_superpoly_fullCoeff,
            xi_scale_spectral_truncation_uniform_superpoly_truncatedCoeff, add_comm]
    _ ≤ (xi_scale_spectral_truncation_uniform_superpoly_tailZeros zeros Γ).sum
        (fun γ => ‖term m γ‖) := norm_sum_le _ _
    _ ≤ xi_scale_spectral_truncation_uniform_superpoly_tailMass zeros weight Γ := by
      refine Finset.sum_le_sum ?_
      intro γ hγ
      have hz : γ ∈ zeros := by
        rw [xi_scale_spectral_truncation_uniform_superpoly_tailZeros] at hγ
        exact (Finset.mem_filter.mp hγ).1
      exact hterm m γ hz
    _ ≤ K A / (Γ : ℝ) ^ A := htail A Γ hΓ

end

end Omega.Zeta
