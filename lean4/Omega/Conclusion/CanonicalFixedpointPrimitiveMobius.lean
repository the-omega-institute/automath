import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.CanonicalSliceExactFixedpointCount

namespace Omega.Conclusion

open Finset

/-- The canonical layer count used in the fixed-point Möbius inversion package. -/
def canonicalLayerPointCount (D : CanonicalSliceData) (k : ℕ) : ℤ :=
  Fintype.card (D.fixedPointsAtLayer k)

/-- The primitive-period count is the Möbius inverse of the layer count. -/
def canonicalPrimitivePointCount (D : CanonicalSliceData) (n : ℕ) : ℤ :=
  ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * canonicalLayerPointCount D (n / d)

/-- The layer count agrees with the closed form `(M + 1)^k`. -/
theorem canonicalLayerPointCount_closed_form (D : CanonicalSliceData) (k : ℕ) :
    canonicalLayerPointCount D k = ((D.M + 1 : ℤ) ^ k) := by
  unfold canonicalLayerPointCount
  exact_mod_cast (paper_conclusion_canonical_slice_exact_fixedpoint_count D k).2

/-- Primitive fixed points on the canonical slice are counted by the Möbius inversion of the
layer counts `k ↦ (M + 1)^k`.
    thm:conclusion-canonical-fixedpoint-primitive-mobius -/
theorem paper_conclusion_canonical_fixedpoint_primitive_mobius (D : CanonicalSliceData) (n : ℕ) :
    canonicalPrimitivePointCount D n =
      ∑ d ∈ Nat.divisors n, ArithmeticFunction.moebius d * ((D.M + 1 : ℤ) ^ (n / d)) := by
  unfold canonicalPrimitivePointCount
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [canonicalLayerPointCount_closed_form]

end Omega.Conclusion
