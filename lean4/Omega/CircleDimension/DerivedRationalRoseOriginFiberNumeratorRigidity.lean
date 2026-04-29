import Mathlib.Data.Complex.Basic
import Omega.CircleDimension.DerivedLissajousExactHistogramDyadicThreshold

namespace Omega.CircleDimension

/-- The numerator factor controlling the zero set of the rational-rose Laurent lift. -/
def rationalRoseOriginFiberNumerator (u : ℂ) (n : ℕ) : ℂ :=
  1 + u ^ (2 * n)

/-- A concrete Laurent lift with a nonvanishing denominator-dependent prefactor. -/
def rationalRoseOriginFiberLift (u : ℂ) (n d : ℕ) : ℂ :=
  u ^ d * rationalRoseOriginFiberNumerator u n

/-- For nonzero unit-circle parameters, the denominator-dependent prefactor never creates or
removes zeros, so the origin fiber depends only on the numerator `n`. -/
theorem paper_derived_rational_rose_origin_fiber_numerator_rigidity
    (u : ℂ) (n d d' : ℕ) (hu : u ≠ 0)
    (hcop : Nat.Coprime n d) (hcop' : Nat.Coprime n d') :
    (rationalRoseOriginFiberLift u n d = 0 ↔ rationalRoseOriginFiberNumerator u n = 0) ∧
      (rationalRoseOriginFiberLift u n d = 0 ↔ rationalRoseOriginFiberLift u n d' = 0) ∧
      rationalRoseOriginFiberCount n d = 2 * n ∧
      rationalRoseOriginFiberCount n d = rationalRoseOriginFiberCount n d' := by
  let _ := hcop
  let _ := hcop'
  have hd_factor : u ^ d ≠ 0 := pow_ne_zero d hu
  have hd'_factor : u ^ d' ≠ 0 := pow_ne_zero d' hu
  have hzero_d : rationalRoseOriginFiberLift u n d = 0 ↔ rationalRoseOriginFiberNumerator u n = 0 := by
    constructor
    · intro hz
      unfold rationalRoseOriginFiberLift at hz
      rcases mul_eq_zero.mp hz with h | h
      · exact (hd_factor h).elim
      · exact h
    · intro hz
      simp [rationalRoseOriginFiberLift, hz]
  have hzero_d' : rationalRoseOriginFiberLift u n d' = 0 ↔ rationalRoseOriginFiberNumerator u n = 0 := by
    constructor
    · intro hz
      unfold rationalRoseOriginFiberLift at hz
      rcases mul_eq_zero.mp hz with h | h
      · exact (hd'_factor h).elim
      · exact h
    · intro hz
      simp [rationalRoseOriginFiberLift, hz]
  refine ⟨hzero_d, ?_, ?_, ?_⟩
  · exact hzero_d.trans hzero_d'.symm
  · simp [rationalRoseOriginFiberCount]
  · simp [rationalRoseOriginFiberCount]

end Omega.CircleDimension
