import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-layer diagonal block package for the gcd algebra. -/
structure conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data where
  Block : Type
  blockDecidableEq : DecidableEq Block
  activeDepths : Finset Block

attribute [instance]
  conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.blockDecidableEq

namespace conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data

/-- Pointwise product on the finite active depth coordinates. -/
def product
    (D : conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data)
    (x y : D.Block → ℚ) (d : D.Block) : ℚ :=
  x d * y d

/-- Active support of a diagonal coordinate vector. -/
def activeSupport
    (D : conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data)
    (x : D.Block → ℚ) : Finset D.Block :=
  D.activeDepths.filter fun d => x d ≠ 0

/-- There are no nonzero nilpotents on active finite-layer diagonal coordinates. -/
def noNonzeroNilpotents
    (D : conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data) :
    Prop :=
  ∀ x : D.Block → ℚ,
    (∀ d ∈ D.activeDepths, D.product x x d = 0) → ∀ d ∈ D.activeDepths, x d = 0

/-- Zero products are exactly products with complementary active support. -/
def zeroProductIffComplementaryActiveSupport
    (D : conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data) :
    Prop :=
  ∀ x y : D.Block → ℚ,
    (∀ d ∈ D.activeDepths, D.product x y d = 0) ↔
      ∀ d ∈ D.activeDepths, d ∈ D.activeSupport x → d ∉ D.activeSupport y

end conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data

/-- Paper label:
`cor:conclusion-fibadic-finite-layer-gcd-reduced-zero-divisor-complement`. -/
theorem paper_conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement
    (D : conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data) :
    D.noNonzeroNilpotents ∧ D.zeroProductIffComplementaryActiveSupport := by
  constructor
  · intro x hx d hd
    exact (mul_eq_zero.mp (hx d hd)).elim id id
  · intro x y
    constructor
    · intro hxy d hd hdx hdy
      have hx : x d ≠ 0 := by
        simpa [conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.activeSupport,
          hd] using hdx
      have hy : y d ≠ 0 := by
        simpa [conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.activeSupport,
          hd] using hdy
      exact (mul_eq_zero.mp (hxy d hd)).elim hx hy
    · intro hcomp d hd
      by_cases hx : x d = 0
      · simp [
          conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.product,
          hx]
      · have hxsupport : d ∈ D.activeSupport x := by
          simp [
            conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.activeSupport,
            hd, hx]
        have hynsupport : d ∉ D.activeSupport y := hcomp d hd hxsupport
        have hy : y d = 0 := by
          by_contra hy
          exact hynsupport (by
            simp [
              conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.activeSupport,
              hd, hy])
        simp [
          conclusion_fibadic_finite_layer_gcd_reduced_zero_divisor_complement_data.product,
          hy]

end Omega.Conclusion
