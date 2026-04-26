import Mathlib.Tactic
import Omega.POM.HankelDeterminantGeometricLaw

namespace Omega.POM

open POMHankelDeterminantGeometricLawData

/-- Concrete carrier for the shifted-Hankel p-adic precision package. The determinant propagation
data is inherited from the chapter-local geometric law, the valuation is recorded multiplicatively,
and the precision profile is read off from the determinant valuation up to a fixed affine offset. -/
structure ConclusionHankelShiftPadicPrecisionSlopeData where
  hankelData : POMHankelDeterminantGeometricLawData
  valuation : ℝ → ℤ
  precision : ℕ → ℤ
  affineOffset : ℤ
  hvaluation_mul : ∀ x y : ℝ, valuation (x * y) = valuation x + valuation y
  hvaluation_pow : ∀ x : ℝ, ∀ r : ℕ, valuation (x ^ r) = (r : ℤ) * valuation x
  hprecision_from_det :
    ∀ r : ℕ,
      precision (hankelData.k0 + r) = valuation (hankelData.determinantSequence r) + affineOffset
  hbase_integral : 0 ≤ precision hankelData.k0
  hslope_nonneg : 0 ≤ valuation hankelData.A.det

namespace ConclusionHankelShiftPadicPrecisionSlopeData

/-- The shifted precision profile is affine with slope `v(det A)`. -/
def fullShiftPrecisionSlope (D : ConclusionHankelShiftPadicPrecisionSlopeData) : Prop :=
  ∀ r : ℕ,
    D.precision (D.hankelData.k0 + r) =
      D.precision D.hankelData.k0 + (r : ℤ) * D.valuation D.hankelData.A.det

/-- The affine precision law keeps the good channel uniformly integral. -/
def goodChannelUniformIntegrality (D : ConclusionHankelShiftPadicPrecisionSlopeData) : Prop :=
  ∀ r : ℕ, 0 ≤ D.precision (D.hankelData.k0 + r)

/-- Successive shifted precisions differ by the constant slope `v(det A)`. -/
def affinePrecisionStratification (D : ConclusionHankelShiftPadicPrecisionSlopeData) : Prop :=
  ∀ r : ℕ,
    D.precision (D.hankelData.k0 + (r + 1)) =
      D.precision (D.hankelData.k0 + r) + D.valuation D.hankelData.A.det

end ConclusionHankelShiftPadicPrecisionSlopeData

open ConclusionHankelShiftPadicPrecisionSlopeData

/-- Paper label: `thm:conclusion-hankel-shift-padic-precision-slope`. The determinant sequence of
the shifted Hankel family is geometric, hence its valuation is affine in the shift parameter; the
same affine law transfers to the p-adic precision profile, yielding uniform integrality and the
constant-slope stratification. -/
theorem paper_conclusion_hankel_shift_padic_precision_slope
    (D : ConclusionHankelShiftPadicPrecisionSlopeData) :
    D.fullShiftPrecisionSlope ∧ D.goodChannelUniformIntegrality ∧
      D.affinePrecisionStratification := by
  have hprecision_zero :
      D.precision D.hankelData.k0 =
        D.valuation ((D.hankelData.H D.hankelData.k0).det) + D.affineOffset := by
    simpa [POMHankelDeterminantGeometricLawData.determinantSequence] using D.hprecision_from_det 0
  have hfull_shift_precision_slope : D.fullShiftPrecisionSlope := by
    intro r
    rw [D.hprecision_from_det r, D.hankelData.determinant_sequence_geometric r]
    calc
      D.valuation ((D.hankelData.H D.hankelData.k0).det * D.hankelData.A.det ^ r) + D.affineOffset
          =
            D.valuation ((D.hankelData.H D.hankelData.k0).det) +
              (r : ℤ) * D.valuation D.hankelData.A.det + D.affineOffset := by
                rw [D.hvaluation_mul, D.hvaluation_pow]
      _ = (D.valuation ((D.hankelData.H D.hankelData.k0).det) + D.affineOffset) +
            (r : ℤ) * D.valuation D.hankelData.A.det := by ring
      _ = D.precision D.hankelData.k0 + (r : ℤ) * D.valuation D.hankelData.A.det := by
            rw [hprecision_zero]
  have hgood_channel_uniform_integrality : D.goodChannelUniformIntegrality := by
    intro r
    rw [hfull_shift_precision_slope r]
    have hr_nonneg : 0 ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
    exact add_nonneg D.hbase_integral (Int.mul_nonneg hr_nonneg D.hslope_nonneg)
  have haffine_precision_stratification : D.affinePrecisionStratification := by
    intro r
    rw [hfull_shift_precision_slope (r + 1), hfull_shift_precision_slope r]
    simp [Nat.cast_add, add_mul, add_assoc, add_comm]
  exact ⟨hfull_shift_precision_slope, hgood_channel_uniform_integrality,
    haffine_precision_stratification⟩

end Omega.POM
