import Mathlib.Tactic
import Omega.Zeta.AbelPowerbaseCovariancePolePowerMap

namespace Omega.Zeta

/-- The renormalized Abel-resolution coefficient attached to the `b`-power subsequence. -/
def abelResolutionErrorCoeff (ψ : ℕ → ℤ) (b : ℕ) : ℕ → ℤ :=
  fun n => ψ (b ^ n) - b ^ n

/-- The same coefficient sequence with the explicit `b^(δ n)` weight attached. -/
def abelResolutionWeightedCoeff (ψ : ℕ → ℤ) (b δ : ℕ) : ℕ → ℤ :=
  fun n => abelResolutionErrorCoeff ψ b n * ((b ^ (δ * n) : ℕ) : ℤ)

/-- Coefficient sequence of the pullback `F(t^k)`. -/
def abelPullbackByPower {α : Type*} [Zero α] (k : ℕ) (a : ℕ → α) : ℕ → α :=
  fun n => if k ∣ n then a (n / k) else 0

/-- The finite root-of-unity filter keeps exactly the coefficients in degrees divisible by `k`. -/
def abelEveryKthFilter {α : Type*} [Zero α] (k : ℕ) (a : ℕ → α) : ℕ → α :=
  fun n => if k ∣ n then a n else 0

private theorem abelResolutionErrorCoeff_powbase
    (ψ : ℕ → ℤ) (b k : ℕ) :
    abelResolutionErrorCoeff ψ (b ^ k) = xiAbelDecimation k (abelResolutionErrorCoeff ψ b) := by
  ext n
  simp [abelResolutionErrorCoeff, xiAbelDecimation, pow_mul]

private theorem abelResolutionWeightedCoeff_powbase
    (ψ : ℕ → ℤ) (b k δ : ℕ) :
    abelResolutionWeightedCoeff ψ (b ^ k) δ =
      xiAbelDecimation k (abelResolutionWeightedCoeff ψ b δ) := by
  ext n
  unfold abelResolutionWeightedCoeff xiAbelDecimation
  have hcoeff :
      abelResolutionErrorCoeff ψ (b ^ k) n = abelResolutionErrorCoeff ψ b (k * n) := by
    simpa [xiAbelDecimation] using congrFun (abelResolutionErrorCoeff_powbase ψ b k) n
  have hpow :
      (b ^ k) ^ (δ * n) = b ^ (δ * (k * n)) := by
    simp [pow_mul, Nat.mul_left_comm]
  rw [hcoeff, hpow]

private theorem abelPullback_decimation_eq_filter
    {α : Type*} [Zero α] (k : ℕ) (hk : 0 < k) (a : ℕ → α) :
    abelPullbackByPower k (xiAbelDecimation k a) = abelEveryKthFilter k a := by
  ext n
  by_cases hkn : k ∣ n
  · rcases hkn with ⟨m, rfl⟩
    simp [abelPullbackByPower, abelEveryKthFilter, xiAbelDecimation, hk.ne']
  · simp [abelPullbackByPower, abelEveryKthFilter, hkn]

/-- Paper label: `thm:abel-resolution-power-renormalization-identity`.
Passing from base `b` to `b^k` renormalizes the Abel-resolution coefficients by `k`-decimation,
and the corresponding formal power series identity is exactly the finite root-of-unity filter
which extracts the coefficients in degrees divisible by `k`. -/
theorem paper_abel_resolution_power_renormalization_identity
    (ψ : ℕ → ℤ) (b k δ : ℕ) (hk : 2 ≤ k) :
    abelResolutionErrorCoeff ψ (b ^ k) = xiAbelDecimation k (abelResolutionErrorCoeff ψ b) ∧
      abelPullbackByPower k (abelResolutionWeightedCoeff ψ (b ^ k) δ) =
        abelEveryKthFilter k (abelResolutionWeightedCoeff ψ b δ) := by
  refine ⟨abelResolutionErrorCoeff_powbase ψ b k, ?_⟩
  calc
    abelPullbackByPower k (abelResolutionWeightedCoeff ψ (b ^ k) δ)
        = abelPullbackByPower k (xiAbelDecimation k (abelResolutionWeightedCoeff ψ b δ)) := by
            rw [abelResolutionWeightedCoeff_powbase ψ b k δ]
    _ = abelEveryKthFilter k (abelResolutionWeightedCoeff ψ b δ) := by
          exact abelPullback_decimation_eq_filter k
            (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk) (abelResolutionWeightedCoeff ψ b δ)

end Omega.Zeta
