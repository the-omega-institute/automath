import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Capacity obtained by truncating only the top fibers of size `M` at budget level `T`. -/
def xiTopGapCapacitySegment (m K M T : ℕ) : ℤ :=
  (2 ^ m : ℤ) - (K : ℤ) * (M : ℤ) + (K : ℤ) * (min M T : ℤ)

/-- Intercept of the affine segment in the top-gap regime. -/
def xiTopGapCapacityIntercept (m K M : ℕ) : ℤ :=
  (2 ^ m : ℤ) - (K : ℤ) * (M : ℤ)

/-- Slope of the affine segment in the top-gap regime. -/
def xiTopGapCapacitySlope (K : ℕ) : ℤ :=
  K

/-- Paper-facing affine segment for the top-gap capacity curve: when the budget lies strictly
below the maximal fiber size, truncation only affects the maximal fibers, so the capacity becomes
an exact affine function of `T` and the unused budget is the top-gap defect. -/
def xiTimePart9tTopGapAffineCapacitySegmentStatement : Prop :=
  ∀ m K M T : ℕ,
    T < M →
      xiTopGapCapacitySegment m K M T =
          (2 ^ m : ℤ) - (K : ℤ) * ((M - T : ℕ) : ℤ) ∧
        xiTopGapCapacitySegment m K M T =
          xiTopGapCapacityIntercept m K M + xiTopGapCapacitySlope K * T ∧
        (2 ^ m : ℤ) - xiTopGapCapacitySegment m K M T =
          (K : ℤ) * ((M - T : ℕ) : ℤ)

theorem paper_xi_time_part9t_top_gap_affine_capacity_segment :
    xiTimePart9tTopGapAffineCapacitySegmentStatement := by
  intro m K M T hT
  have hle : T ≤ M := Nat.le_of_lt hT
  have hminz : min (M : ℤ) (T : ℤ) = (T : ℤ) := by
    exact min_eq_right (by exact_mod_cast hle)
  have hsub : (((M - T : ℕ) : ℤ)) = (M : ℤ) - (T : ℤ) := by
    exact Int.ofNat_sub hle
  constructor
  · rw [xiTopGapCapacitySegment, hminz, hsub]
    ring
  constructor
  · rw [xiTopGapCapacitySegment, xiTopGapCapacityIntercept, xiTopGapCapacitySlope, hminz]
  · rw [xiTopGapCapacitySegment, hminz, hsub]
    ring

end Omega.Zeta
