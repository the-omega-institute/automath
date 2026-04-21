import Mathlib.Tactic

namespace Omega.Zeta

/-- The coefficient sequence extracted from the `b`-power subsequence of a master sequence. -/
def xiAbelCoeff (ψ : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  fun n => ψ (b ^ n)

/-- Damping multiplies the `n`-th coefficient by the explicit `b^(δ n)` factor. -/
def xiAbelDampedSeries (ψ : ℕ → ℕ) (b δ : ℕ) : ℕ → ℕ :=
  fun n => xiAbelCoeff ψ b n * b ^ (δ * n)

/-- The analytic remainder is encoded by the same powerbase sampling rule. -/
def xiAbelAnalyticRemainder (h : ℕ → ℕ) (b δ : ℕ) : ℕ → ℕ :=
  fun n => h (b ^ n) * b ^ (δ * n)

/-- Decimation keeps every `m`-th coefficient. -/
def xiAbelDecimation {α : Type*} (m : ℕ) (a : ℕ → α) : ℕ → α :=
  fun n => a (m * n)

/-- The pole position attached to the exponent pair `(ρ, δ)`. -/
def xiAbelPoleMap (b ρ δ : ℕ) : ℕ :=
  b ^ (ρ + δ)

/-- Paper label: `thm:xi-abel-powerbase-covariance-pole-power-map`.
Passing from `b` to `b^m` decimates the coefficient and remainder sequences, and the pole map
raises to the `m`-th power. -/
theorem paper_xi_abel_powerbase_covariance_pole_power_map
    (ψ h : ℕ → ℕ) (b m ρ δ : ℕ) :
    xiAbelCoeff ψ (b ^ m) = xiAbelDecimation m (xiAbelCoeff ψ b) ∧
      xiAbelDampedSeries ψ (b ^ m) δ = xiAbelDecimation m (xiAbelDampedSeries ψ b δ) ∧
      xiAbelAnalyticRemainder h (b ^ m) δ =
        xiAbelDecimation m (xiAbelAnalyticRemainder h b δ) ∧
      xiAbelPoleMap (b ^ m) ρ δ = (xiAbelPoleMap b ρ δ) ^ m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext n
    simp [xiAbelCoeff, xiAbelDecimation, pow_mul]
  · ext n
    simp [xiAbelDampedSeries, xiAbelCoeff, xiAbelDecimation, pow_mul, Nat.mul_left_comm]
  · ext n
    simp [xiAbelAnalyticRemainder, xiAbelDecimation, pow_mul, Nat.mul_left_comm]
  · calc
      xiAbelPoleMap (b ^ m) ρ δ = b ^ (m * (ρ + δ)) := by
        rw [xiAbelPoleMap, ← pow_mul]
      _ = b ^ ((ρ + δ) * m) := by rw [Nat.mul_comm]
      _ = (xiAbelPoleMap b ρ δ) ^ m := by
        rw [xiAbelPoleMap, pow_mul]

end Omega.Zeta
