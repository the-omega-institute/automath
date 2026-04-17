import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace Omega.TypedAddressBiaxialCompletion

/-- Compactify the radial coordinate to a phase-box coordinate. -/
noncomputable def xiCompactify (x : ℝ) : ℝ :=
  Real.arctan x / Real.pi

/-- Recover the radial coordinate from the phase-box coordinate. -/
noncomputable def xiUncompactify (u : ℝ) : ℝ :=
  Real.tan (Real.pi * u)

/-- The local Jacobian amplification factor of the inverse compactification map. -/
noncomputable def xiJacobianAmplification (x : ℝ) : ℝ :=
  Real.pi * (1 + x ^ 2)

/-- Width of an `n`-bit dyadic bracket in the compactified coordinate. -/
noncomputable def xiDyadicWidth (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹

/-- Protocol-level admissibility: the dyadic width is small enough to certify `x`
within the absolute error budget `ε`. -/
def xiCertifiedRadialReadout (x ε : ℝ) (n : ℕ) : Prop :=
  xiDyadicWidth n ≤ ε / xiJacobianAmplification x

theorem xiJacobianAmplification_pos (x : ℝ) : 0 < xiJacobianAmplification x := by
  dsimp [xiJacobianAmplification]
  positivity

/-- If an `n`-bit dyadic bracket is narrow enough to certify `x` with absolute error `ε`,
then the bit count dominates the base-2 logarithm of the Jacobian amplification ratio.
    thm:xi-radial-information-projection-lower-bound -/
theorem paper_xi_radial_information_projection_lower_bound (x ε : ℝ) (n : ℕ)
    (hε : 0 < ε) (hcert : xiCertifiedRadialReadout x ε n) :
    Real.logb 2 (xiJacobianAmplification x / ε) ≤ n := by
  have hJpos : 0 < xiJacobianAmplification x := xiJacobianAmplification_pos x
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  have hbound : xiJacobianAmplification x ≤ ε * (2 : ℝ) ^ n := by
    rw [xiCertifiedRadialReadout, xiDyadicWidth] at hcert
    have htmp := hcert
    field_simp [hJpos.ne', hpowpos.ne'] at htmp
    simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
  have hratio : xiJacobianAmplification x / ε ≤ (2 : ℝ) ^ n := by
    rw [_root_.div_le_iff₀ hε]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbound
  have hratio_pos : 0 < xiJacobianAmplification x / ε := by positivity
  have hratio' : xiJacobianAmplification x / ε ≤ (2 : ℝ) ^ (n : ℝ) := by
    simpa [Real.rpow_natCast] using hratio
  exact (Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (hb := by norm_num) hratio_pos).2 hratio'

end Omega.TypedAddressBiaxialCompletion
