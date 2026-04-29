import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.CanonicalFixedpointPrimitiveMobius

namespace Omega.Conclusion

open Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-- Paper label: `cor:conclusion-canonical-fixedpoint-lambert-witt-series`. -/
theorem paper_conclusion_canonical_fixedpoint_lambert_witt_series
    (D : CanonicalSliceData) {n : ℕ} (hn : 0 < n) :
    ((D.M + 1 : ℤ) ^ n) =
      ∑ d ∈ Nat.divisors n, canonicalPrimitivePointCount D d := by
  have hsum :
      (∑ d ∈ Nat.divisors n, canonicalPrimitivePointCount D d) =
        canonicalLayerPointCount D n := by
    let s : Set ℕ := Set.univ
    have hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s := by
      intro _ _ _ _
      trivial
    have hprimitive :
        ∀ u > 0, u ∈ s →
          (∑ x ∈ Nat.divisorsAntidiagonal u,
              (ArithmeticFunction.moebius x.fst : ℤ) * canonicalLayerPointCount D x.snd) =
            canonicalPrimitivePointCount D u := by
      intro u _hu _hsu
      rw [canonicalPrimitivePointCount]
      exact Nat.sum_divisorsAntidiagonal
        (fun d e => (ArithmeticFunction.moebius d : ℤ) * canonicalLayerPointCount D e)
    exact
      (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ) s hs
        (f := canonicalPrimitivePointCount D)
        (g := canonicalLayerPointCount D)).mpr hprimitive n hn trivial
  rw [canonicalLayerPointCount_closed_form] at hsum
  exact hsum.symm

end Omega.Conclusion
