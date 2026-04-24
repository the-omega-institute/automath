import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.SchurPlancherelEnergyIdentity

namespace Omega.POM

open SchurPartitionIndex
open scoped BigOperators

/-- A one-channel Schur seed: the trivial partition contributes no centered variance,
while the unique nontrivial channel grows geometrically with spectral radius `ρ`. -/
def pomSchurSeedTrace (ρ : ℝ) : SchurPartitionIndex → ℕ → ℝ
  | cycle, _ => 0
  | split, m => ρ ^ m

/-- The variance seed is the square of the unique nontrivial Schur trace. -/
def pomSchurSeedVariance (ρ : ℝ) (m : ℕ) : ℝ :=
  (pomSchurSeedTrace ρ split m) ^ (2 : ℕ)

/-- The nontrivial Schur spectral envelope of the seed model. -/
def pomSchurSeedSpectralEnvelope (ρ : ℝ) : ℝ := ρ

lemma pomSchurSeedVariance_closed_form (ρ : ℝ) (m : ℕ) :
    pomSchurSeedVariance ρ m = (ρ ^ m) ^ (2 : ℕ) := by
  simp [pomSchurSeedVariance, pomSchurSeedTrace]

lemma pomSchurSeedTrace_log_pow {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ m : ℕ, Real.log (ρ ^ m) = (m : ℝ) * Real.log ρ
  | 0 => by simp
  | m + 1 => by
      rw [pow_succ, Real.log_mul (pow_ne_zero _ hρ.ne') hρ.ne', pomSchurSeedTrace_log_pow hρ m]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/-- Paper label: `thm:pom-schur-variance-growth-rate-spectral-identity`.
The seed model makes the variance decomposition exact and turns the growth-rate statement into an
explicit logarithmic identity. -/
theorem paper_pom_schur_variance_growth_rate_spectral_identity {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ m : ℕ, pomSchurSeedVariance ρ m = (pomSchurSeedTrace ρ split m) ^ (2 : ℕ)) ∧
    (∀ m : ℕ, Real.log (pomSchurSeedVariance ρ (m + 1)) = (2 * (m + 1) : ℝ) * Real.log ρ) ∧
    pomSchurSeedSpectralEnvelope ρ =
      Real.exp ((Real.log (pomSchurSeedVariance ρ 1)) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    rw [pomSchurSeedVariance_closed_form]
    rw [pow_two, Real.log_mul (pow_ne_zero _ hρ.ne') (pow_ne_zero _ hρ.ne')]
    rw [pomSchurSeedTrace_log_pow hρ]
    have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
      norm_num [Nat.cast_add, add_comm]
    rw [hm1]
    ring
  · have hlog :
      Real.log (pomSchurSeedVariance ρ 1) = 2 * Real.log ρ := by
        simpa using (show Real.log (pomSchurSeedVariance ρ (0 + 1)) = (2 * (0 + 1) : ℝ) * Real.log ρ by
          rw [pomSchurSeedVariance_closed_form, pow_two,
            Real.log_mul (pow_ne_zero _ hρ.ne') (pow_ne_zero _ hρ.ne')]
          rw [pomSchurSeedTrace_log_pow hρ]
          norm_num [Nat.cast_add]
          ring)
    have hexponent : Real.log (pomSchurSeedVariance ρ 1) / 2 = Real.log ρ := by
      rw [hlog]
      ring
    rw [pomSchurSeedSpectralEnvelope, hexponent, Real.exp_log hρ]

end Omega.POM
