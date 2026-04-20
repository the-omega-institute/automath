import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangChebyshevSemiconjugacy

namespace Omega.UnitCirclePhaseArithmetic

/-- The cosine-squared endpoint value appearing on the Lee--Yang singular ray. -/
noncomputable def leyangEndpointCos2Spectrum (θ : ℝ) : ℝ :=
  -(1 / (4 * Real.cos θ ^ 2))

/-- The endpoint preimage package: on the unit circle, the `n`th induced Lee--Yang iterate lands
at the two endpoint traces exactly when the `2n`th power closes up, and the resulting endpoint
values are the expected cosine-squared coordinates. -/
def LeyangEndpointPreimageCos2SpectrumLaw (n : ℕ) : Prop :=
  (∀ z : ℂ, ‖z‖ = 1 →
      ((leyangFn n (leyangTau z) = 1 ∨ leyangFn n (leyangTau z) = -1) ↔ z ^ (2 * n) = 1)) ∧
    ∀ θ : ℝ, leyangEndpointCos2Spectrum θ = -(1 / (4 * Real.cos θ ^ 2))

private theorem pow_eq_one_or_neg_one_iff_sq_eq_one (z : ℂ) (n : ℕ) :
    (z ^ n = 1 ∨ z ^ n = -1) ↔ z ^ (2 * n) = 1 := by
  constructor
  · intro h
    rcases h with h | h
    · calc
        z ^ (2 * n) = (z ^ n) ^ 2 := by
          rw [Nat.mul_comm, pow_mul]
        _ = 1 := by simp [h]
    · calc
        z ^ (2 * n) = (z ^ n) ^ 2 := by
          rw [Nat.mul_comm, pow_mul]
        _ = 1 := by simp [h]
  · intro h
    have hsquare : (z ^ n) ^ 2 = 1 := by
      simpa [Nat.mul_comm, pow_mul] using h
    have hzero : (z ^ n - 1) * (z ^ n + 1) = 0 := by
      calc
        (z ^ n - 1) * (z ^ n + 1) = (z ^ n) ^ 2 - 1 := by ring
        _ = 1 - 1 := by rw [hsquare]
        _ = 0 := by ring
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with hminus | hplus
    · left
      exact sub_eq_zero.mp hminus
    · right
      simpa using eq_neg_of_add_eq_zero_left hplus

/-- Solving the endpoint equation on the Lee--Yang singular ray amounts to pulling back to the
unit circle, where the `n`th induced iterate hits the endpoint traces exactly at the `2n`-torsion
points, and the endpoint values are the cosine-squared spectrum.
    cor:leyang-endpoint-preimage-cos2-spectrum -/
theorem paper_leyang_endpoint_preimage_cos2_spectrum (n : ℕ) (hn : 2 ≤ n) :
    LeyangEndpointPreimageCos2SpectrumLaw n := by
  have hsemiconj := paper_leyang_chebyshev_semiconjugacy 1 n (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro z
    refine fun hz => ?_
    have hnorm_ne_zero : ‖z‖ ≠ 0 := by
      simp [hz]
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hnorm_ne_zero (by simpa [hz0])
    have htau0 : leyangTau z ≠ 0 := by simp [leyangTau, hz0]
    have hsemi : leyangFn n (leyangTau z) = leyangTau (z ^ n) := by
      simpa using (hsemiconj.1 z hz htau0).symm
    calc
      (leyangFn n (leyangTau z) = 1 ∨ leyangFn n (leyangTau z) = -1) ↔
          (leyangTau (z ^ n) = 1 ∨ leyangTau (z ^ n) = -1) := by rw [hsemi]
      _ ↔ z ^ (2 * n) = 1 := by
          simpa [leyangTau] using pow_eq_one_or_neg_one_iff_sq_eq_one z n
  · intro θ
    rfl

end Omega.UnitCirclePhaseArithmetic
