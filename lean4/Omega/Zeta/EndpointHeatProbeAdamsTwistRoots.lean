import Mathlib
import Omega.Zeta.AdamsBinomialProbeFourierDiagonalization

namespace Omega.Zeta

open scoped BigOperators
open Classical

noncomputable section

/-- The endpoint probe reuses the Fourier-diagonalized Adams binomial probe series. -/
noncomputable def adamsBinomialProbeEndpointHeatProbe
    (N d : Nat) (c : Int → Complex) (omega : Units Complex) : Complex :=
  adamsBinomialProbeFourierSeries N d c omega

/-- The concrete `d`-th root target singled out by the Adams twist `omega`. -/
def adamsTwistRootCondition (d : Nat) (omega z : Units Complex) : Prop :=
  (z : Complex) ^ d = -((omega : Complex)⁻¹)

/-- The root-target indicator used in the finite binomial expansion. -/
noncomputable def adamsTwistRootIndicator (d : Nat) (omega z : Units Complex) : ℝ :=
  if adamsTwistRootCondition d omega z then 1 else 0

/-- The finite binomial expansion that models the endpoint heat-probe quadratic form. -/
noncomputable def adamsTwistRootQuadraticForm (N d : Nat) (omega z : Units Complex) : ℝ :=
  (1 / 2 : ℝ) ^ N *
    Finset.sum (Finset.range (N + 1))
      (fun k => (Nat.choose N k : ℝ) * (adamsTwistRootIndicator d omega z) ^ k)

/-- The explicit kernel extracted from the finite binomial expansion. -/
noncomputable def adamsTwistRootKernel (N d : Nat) (omega z : Units Complex) : ℝ :=
  if adamsTwistRootCondition d omega z then 1 else (1 / 2 : ℝ) ^ N

/-- The limiting target value supported on the `d`-th root locus. -/
noncomputable def adamsTwistRootTargetValue (d : Nat) (omega z : Units Complex) : ℝ :=
  if adamsTwistRootCondition d omega z then 1 else 0

/-- Concrete package for the Adams-twisted endpoint probe: the probe agrees with the existing
Fourier series, the finite binomial quadratic form collapses to the explicit root-target kernel,
that kernel is monotone in `N`, and it dominates the limiting root target. -/
def adamsBinomialProbeRootTargetPackage
    (N d : Nat) (c : Int → Complex) (omega : Units Complex) : Prop :=
  adamsBinomialProbeEndpointHeatProbe N d c omega = adamsBinomialProbeFourierSeries N d c omega ∧
    ∀ z : Units Complex,
      adamsTwistRootQuadraticForm N d omega z = adamsTwistRootKernel N d omega z ∧
        adamsTwistRootKernel (N + 1) d omega z ≤ adamsTwistRootKernel N d omega z ∧
        adamsTwistRootTargetValue d omega z ≤ adamsTwistRootKernel N d omega z

/-- Paper-facing Adams-twisted endpoint heat-probe package.
    thm:xi-endpoint-heat-probe-adams-twist-roots -/
theorem paper_xi_endpoint_heat_probe_adams_twist_roots
    (N d : Nat) (c : Int → Complex) (omega : Units Complex) :
    adamsBinomialProbeRootTargetPackage N d c omega := by
  refine ⟨rfl, ?_⟩
  intro z
  by_cases hroot : adamsTwistRootCondition d omega z
  · have hsumNat : Finset.sum (Finset.range (N + 1)) (fun k => Nat.choose N k) = 2 ^ N := by
      simpa using Nat.sum_range_choose N
    have hsum :
        Finset.sum (Finset.range (N + 1)) (fun k => (Nat.choose N k : ℝ)) = (2 : ℝ) ^ N := by
      exact_mod_cast hsumNat
    refine ⟨?_, ?_, ?_⟩
    · calc
        adamsTwistRootQuadraticForm N d omega z
            = (1 / 2 : ℝ) ^ N * Finset.sum (Finset.range (N + 1)) (fun k =>
                (Nat.choose N k : ℝ)) := by
                simp [adamsTwistRootQuadraticForm, adamsTwistRootIndicator, hroot]
        _ = (1 / 2 : ℝ) ^ N * (2 : ℝ) ^ N := by rw [hsum]
        _ = 1 := by
              rw [← mul_pow]
              norm_num
        _ = adamsTwistRootKernel N d omega z := by simp [adamsTwistRootKernel, hroot]
    · simp [adamsTwistRootKernel, hroot]
    · simp [adamsTwistRootTargetValue, adamsTwistRootKernel, hroot]
  · have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have hsum_zero :
        Finset.sum (Finset.range (N + 1)) (fun x => (Nat.choose N x : ℝ) * 0 ^ x) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b hb hb0
        simp [hb0]
      · simp
    have hmono_half : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ N := by
      rw [pow_succ]
      have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := pow_nonneg hhalf_nonneg N
      nlinarith
    refine ⟨?_, ?_, ?_⟩
    · calc
        adamsTwistRootQuadraticForm N d omega z
            = (1 / 2 : ℝ) ^ N *
                Finset.sum (Finset.range (N + 1)) (fun x => (Nat.choose N x : ℝ) * 0 ^ x) := by
          simp [adamsTwistRootQuadraticForm, adamsTwistRootIndicator, hroot]
        _ = (1 / 2 : ℝ) ^ N := by rw [hsum_zero, mul_one]
        _ = adamsTwistRootKernel N d omega z := by simp [adamsTwistRootKernel, hroot]
    · simpa [adamsTwistRootKernel, hroot] using hmono_half
    · simp [adamsTwistRootTargetValue, adamsTwistRootKernel, hroot]

end

end Omega.Zeta
