import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Omega.Zeta.XiGridScanDiophantineDealiasingStability

namespace Omega.Zeta

noncomputable section

/-- The linearized two-scale comoving channel with step size `α`. -/
def xi_two_scale_comoving_spectrum_diophantine_threshold_channel
    (α γ δ : ℝ) : ℝ :=
  γ + α * δ

/-- Reconstruction formula for the defect parameter `δ` from two channel readouts. -/
def xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta
    (α₁ α₂ y₁ y₂ : ℝ) : ℝ :=
  (y₂ - y₁) / (α₂ - α₁)

/-- Reconstruction formula for the base coordinate `γ` after recovering `δ`. -/
def xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma
    (α₁ α₂ y₁ y₂ : ℝ) : ℝ :=
  y₁ - α₁ *
    xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta α₁ α₂ y₁ y₂

lemma xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta_exact
    {α₁ α₂ γ δ : ℝ}
    (hα : α₁ ≠ α₂) :
    xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta
        α₁ α₂
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₁ γ δ)
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₂ γ δ) =
      δ := by
  have hα' : α₂ ≠ α₁ := Ne.symm hα
  have hden : α₂ - α₁ ≠ 0 := sub_ne_zero.mpr hα'
  unfold xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta
    xi_two_scale_comoving_spectrum_diophantine_threshold_channel
  field_simp [hden]
  ring

lemma xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma_exact
    {α₁ α₂ γ δ : ℝ}
    (hα : α₁ ≠ α₂) :
    xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma
        α₁ α₂
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₁ γ δ)
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₂ γ δ) =
      γ := by
  unfold xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma
  rw [xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta_exact hα]
  unfold xi_two_scale_comoving_spectrum_diophantine_threshold_channel
  ring

lemma xi_two_scale_comoving_spectrum_diophantine_threshold_lifts_zero
    {Δ₁ Δ₂ : ℝ} (hIrr : Irrational (Δ₁ / Δ₂)) (hΔ₂ : 0 < Δ₂)
    {k₁ k₂ : ℤ} (heq : (k₁ : ℝ) * Δ₁ = (k₂ : ℝ) * Δ₂) :
    k₁ = 0 ∧ k₂ = 0 := by
  by_cases hk₁ : k₁ = 0
  · constructor
    · exact hk₁
    · by_cases hk₂ : k₂ = 0
      · exact hk₂
      · exfalso
        rw [hk₁, Int.cast_zero, zero_mul] at heq
        have hk₂R : (k₂ : ℝ) ≠ 0 := by exact_mod_cast hk₂
        have hΔ₂_zero : Δ₂ = 0 := by
          have hprod : (k₂ : ℝ) * Δ₂ = 0 := heq.symm
          rcases mul_eq_zero.mp hprod with hk₂_zero | hΔ₂_zero
          · exact (hk₂R hk₂_zero).elim
          · exact hΔ₂_zero
        exact hΔ₂.ne' hΔ₂_zero
  · have hk₁R : (k₁ : ℝ) ≠ 0 := by exact_mod_cast hk₁
    have hratio : Δ₁ / Δ₂ = (k₂ : ℝ) / (k₁ : ℝ) := by
      field_simp [hΔ₂.ne', hk₁R]
      nlinarith [heq]
    exfalso
    exact ((irrational_iff_ne_rational _).mp hIrr k₂ k₁ hk₁) <| by simpa using hratio

lemma xi_two_scale_comoving_spectrum_diophantine_threshold_gamma_injective
    {Δ₁ Δ₂ γ γ' : ℝ} (hIrr : Irrational (Δ₁ / Δ₂)) (hΔ₂ : 0 < Δ₂)
    {k₁ k₂ : ℤ}
    (hγ₁ : γ' = γ + (k₁ : ℝ) * Δ₁)
    (hγ₂ : γ' = γ + (k₂ : ℝ) * Δ₂) :
    γ' = γ ∧ k₁ = 0 ∧ k₂ = 0 := by
  have heq : (k₁ : ℝ) * Δ₁ = (k₂ : ℝ) * Δ₂ := by
    nlinarith [hγ₁, hγ₂]
  have hk : k₁ = 0 ∧ k₂ = 0 :=
    xi_two_scale_comoving_spectrum_diophantine_threshold_lifts_zero hIrr hΔ₂ heq
  rcases hk with ⟨hk₁, hk₂⟩
  constructor
  · rw [hγ₁, hk₁]
    ring
  · exact ⟨hk₁, hk₂⟩

/-- Paper label: `thm:xi-two-scale-comoving-spectrum-diophantine-threshold`. Two distinct scales
recover `δ` and then `γ` exactly from the paired channel readouts; an irrational step ratio rules
out nonzero lift integers and therefore makes the comoving `γ` coordinate injective; and a
uniform Diophantine lower bound yields the advertised polynomial stability estimate for both scan
channels. -/
theorem paper_xi_two_scale_comoving_spectrum_diophantine_threshold
    {α₁ α₂ γ γ' δ : ℝ} (hα : α₁ ≠ α₂)
    {Δ₁ Δ₂ : ℝ} (hIrr : Irrational (Δ₁ / Δ₂)) (hΔ₂ : 0 < Δ₂)
    {k₁ k₂ : ℤ}
    (hγ₁ : γ' = γ + (k₁ : ℝ) * Δ₁)
    (hγ₂ : γ' = γ + (k₂ : ℝ) * Δ₂)
    (target : ℝ) (scan₁ scan₂ : ℕ → ℚ) (C : ℝ) (τ : ℕ) (hC : 0 < C)
    (hDioph₁ : xiGridScanDiophantineLowerBound target scan₁ C τ)
    (hDioph₂ : xiGridScanDiophantineLowerBound target scan₂ C τ) :
    xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta
        α₁ α₂
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₁ γ δ)
        (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₂ γ δ) =
      δ ∧
      xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma
          α₁ α₂
          (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₁ γ δ)
          (xi_two_scale_comoving_spectrum_diophantine_threshold_channel α₂ γ δ) =
        γ ∧
      γ' = γ ∧
      k₁ = 0 ∧
      k₂ = 0 ∧
      ∀ n : ℕ,
        xiGridScanConditionNumber target (scan₁ n) ≤ ((n + 1 : ℝ) ^ τ) / C ∧
          xiGridScanConditionNumber target (scan₂ n) ≤ ((n + 1 : ℝ) ^ τ) / C := by
  have hγ :
      γ' = γ ∧ k₁ = 0 ∧ k₂ = 0 :=
    xi_two_scale_comoving_spectrum_diophantine_threshold_gamma_injective hIrr hΔ₂ hγ₁ hγ₂
  have hstable :=
    (paper_xi_grid_scan_diophantine_dealiasing_stability
      target scan₁ scan₂ C τ hC).1 ⟨hDioph₁, hDioph₂⟩
  rcases hγ with ⟨hγ', hk₁, hk₂⟩
  refine ⟨?_, ?_, hγ', hk₁, hk₂, hstable⟩
  · exact xi_two_scale_comoving_spectrum_diophantine_threshold_recover_delta_exact hα
  · exact xi_two_scale_comoving_spectrum_diophantine_threshold_recover_gamma_exact hα

end

end Omega.Zeta
