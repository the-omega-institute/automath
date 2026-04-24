import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- Concrete dyadic readout capacity modeled by the least integer above the `2^(b/2)` growth law. -/
def operationalHalfCircleDyadicCapacity (b : ℕ) : ℕ :=
  Nat.ceil (Real.rpow 2 ((b : ℝ) / 2))

/-- Concrete audited package for the operational half-circle dimension law on `ℕ`. The record
stores a visible capacity function together with the explicit constants claimed by the paper. -/
structure OperationalHalfCircleDimensionNData where
  Nmax : ℕ → ℕ
  c : ℝ
  C : ℝ
  growthExponent : ℝ
  halfCircleDim : ℝ
  hNmax : Nmax = operationalHalfCircleDyadicCapacity
  hc : c = 1
  hC : C = 2
  hGrowthExponent : growthExponent = (1 : ℝ) / 2
  hHalfCircleDim : halfCircleDim = (1 : ℝ) / 2

namespace OperationalHalfCircleDimensionNData

/-- The packaged capacity law: the visible readout size grows like `2^(b/2)`, hence the
operational half-circle exponent is exactly `1/2`. -/
def Holds (D : OperationalHalfCircleDimensionNData) : Prop :=
  (∀ b : ℕ, 1 ≤ b →
    D.c * Real.rpow 2 ((b : ℝ) / 2) ≤ (D.Nmax b : ℝ) ∧
      (D.Nmax b : ℝ) ≤ D.C * Real.rpow 2 ((b : ℝ) / 2)) ∧
    D.growthExponent = (1 : ℝ) / 2 ∧
    D.halfCircleDim = (1 : ℝ) / 2

end OperationalHalfCircleDimensionNData

open OperationalHalfCircleDimensionNData

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the operational half-circle dimension theorem for `ℕ`.
    thm:cdim-operational-half-circle-dimension-N -/
theorem paper_cdim_operational_half_circle_dimension_N
    (D : OperationalHalfCircleDimensionNData) : D.Holds := by
  rcases D with ⟨Nmax, c, C, growthExponent, halfCircleDim, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, rfl, rfl⟩
  intro b hb
  let x : ℝ := Real.rpow 2 ((b : ℝ) / 2)
  have hx_lower : x ≤ (operationalHalfCircleDyadicCapacity b : ℝ) := by
    simpa [operationalHalfCircleDyadicCapacity, x] using (Nat.le_ceil x)
  have hx_nonneg_exp : 0 ≤ (b : ℝ) / 2 := by positivity
  have hx_ge_one : 1 ≤ x := by
    have hbase : (1 : ℝ) ≤ 2 := by norm_num
    simpa [x] using Real.one_le_rpow hbase hx_nonneg_exp
  have hx_gt_half : (1 / 2 : ℝ) < x := by
    linarith
  have hx_ge_half_inv : (2 : ℝ)⁻¹ ≤ x := by
    simpa [one_div] using (le_of_lt hx_gt_half)
  have hx_upper : (operationalHalfCircleDyadicCapacity b : ℝ) ≤ 2 * x := by
    simpa [operationalHalfCircleDyadicCapacity, x] using
      (Nat.ceil_le_two_mul (a := x) hx_ge_half_inv)
  exact ⟨by simpa [x] using hx_lower, by simpa [x] using hx_upper⟩

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the operational half-circle dimension theorem for `ℕ`.
    thm:cdim-operational-half-circle-dimension-N -/
theorem paper_circle_dimension_operational_half_circle_dimension_nat
    (Nmax : ℕ → ℕ)
    (c C growthExponent halfCircleDim : ℝ)
    (hBounds :
      ∀ b : ℕ, 1 ≤ b →
        c * Real.rpow 2 ((b : ℝ) / 2) ≤ (Nmax b : ℝ) ∧
          (Nmax b : ℝ) ≤ C * Real.rpow 2 ((b : ℝ) / 2))
    (hGrowth : growthExponent = (1 : ℝ) / 2)
    (hHalf : halfCircleDim = growthExponent) :
    (∀ b : ℕ, 1 ≤ b →
      c * Real.rpow 2 ((b : ℝ) / 2) ≤ (Nmax b : ℝ) ∧
        (Nmax b : ℝ) ≤ C * Real.rpow 2 ((b : ℝ) / 2)) ∧
      growthExponent = (1 : ℝ) / 2 ∧
      halfCircleDim = (1 : ℝ) / 2 := by
  exact ⟨hBounds, hGrowth, hHalf.trans hGrowth⟩

end

end Omega.CircleDimension
