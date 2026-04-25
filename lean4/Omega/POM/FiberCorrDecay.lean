import Mathlib

namespace Omega.POM

open scoped BigOperators

/-- Concrete twisted transfer operator on the two nontrivial fiber characters. -/
def pom_fiber_corr_decay_twistedTransfer (ρ : Fin 2 → ℝ) (χ : Fin 2) : ℝ :=
  ρ χ

/-- Fiber correlation written as the sum of the two nontrivial twisted channels. -/
def pom_fiber_corr_decay_correlation (coeff ρ : Fin 2 → ℝ) (n : ℕ) : ℝ :=
  ∑ χ : Fin 2, (coeff χ) ^ (2 : ℕ) * (pom_fiber_corr_decay_twistedTransfer ρ χ) ^ n

/-- Parseval energy of the nontrivial fiber observable. -/
def pom_fiber_corr_decay_parsevalEnergy (coeff : Fin 2 → ℝ) : ℝ :=
  ∑ χ : Fin 2, (coeff χ) ^ (2 : ℕ)

/-- Worst normalized spectral radius among the two nontrivial twists. -/
def pom_fiber_corr_decay_worstTwist (ρ : Fin 2 → ℝ) : ℝ :=
  max (pom_fiber_corr_decay_twistedTransfer ρ 0) (pom_fiber_corr_decay_twistedTransfer ρ 1)

/-- Paper label: `thm:pom-fiber-corr-decay`.
Expanding the fiber observable into the two nontrivial character channels makes the correlation a
sum of twisted-transfer contributions. Bounding each channel by the worst normalized spectral
radius and collecting the squared Fourier coefficients by Parseval gives the decay envelope. -/
theorem paper_pom_fiber_corr_decay (coeff ρ : Fin 2 → ℝ) (n : ℕ)
    (hρ : ∀ χ : Fin 2, 0 ≤ pom_fiber_corr_decay_twistedTransfer ρ χ) :
    |pom_fiber_corr_decay_correlation coeff ρ n| ≤
      pom_fiber_corr_decay_parsevalEnergy coeff * pom_fiber_corr_decay_worstTwist ρ ^ n := by
  have hpow0 :
      (pom_fiber_corr_decay_twistedTransfer ρ 0) ^ n ≤ pom_fiber_corr_decay_worstTwist ρ ^ n := by
    exact pow_le_pow_left₀ (hρ 0) (le_max_left _ _) _
  have hpow1 :
      (pom_fiber_corr_decay_twistedTransfer ρ 1) ^ n ≤ pom_fiber_corr_decay_worstTwist ρ ^ n := by
    exact pow_le_pow_left₀ (hρ 1) (le_max_right _ _) _
  have hterm0 :
      (coeff 0) ^ (2 : ℕ) * (pom_fiber_corr_decay_twistedTransfer ρ 0) ^ n ≤
        (coeff 0) ^ (2 : ℕ) * pom_fiber_corr_decay_worstTwist ρ ^ n := by
    exact mul_le_mul_of_nonneg_left hpow0 (sq_nonneg _)
  have hterm1 :
      (coeff 1) ^ (2 : ℕ) * (pom_fiber_corr_decay_twistedTransfer ρ 1) ^ n ≤
        (coeff 1) ^ (2 : ℕ) * pom_fiber_corr_decay_worstTwist ρ ^ n := by
    exact mul_le_mul_of_nonneg_left hpow1 (sq_nonneg _)
  have hcorr_nonneg : 0 ≤ pom_fiber_corr_decay_correlation coeff ρ n := by
    rw [pom_fiber_corr_decay_correlation, Fin.sum_univ_two]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (hρ 0) _))
      (mul_nonneg (sq_nonneg _) (pow_nonneg (hρ 1) _))
  rw [abs_of_nonneg hcorr_nonneg, pom_fiber_corr_decay_correlation, Fin.sum_univ_two]
  calc
    (coeff 0) ^ (2 : ℕ) * (pom_fiber_corr_decay_twistedTransfer ρ 0) ^ n +
        (coeff 1) ^ (2 : ℕ) * (pom_fiber_corr_decay_twistedTransfer ρ 1) ^ n
      ≤ (coeff 0) ^ (2 : ℕ) * pom_fiber_corr_decay_worstTwist ρ ^ n +
          (coeff 1) ^ (2 : ℕ) * pom_fiber_corr_decay_worstTwist ρ ^ n := add_le_add hterm0 hterm1
    _ = ((coeff 0) ^ (2 : ℕ) + (coeff 1) ^ (2 : ℕ)) * pom_fiber_corr_decay_worstTwist ρ ^ n := by
      ring
    _ = pom_fiber_corr_decay_parsevalEnergy coeff * pom_fiber_corr_decay_worstTwist ρ ^ n := by
      rw [pom_fiber_corr_decay_parsevalEnergy, Fin.sum_univ_two]

end Omega.POM
