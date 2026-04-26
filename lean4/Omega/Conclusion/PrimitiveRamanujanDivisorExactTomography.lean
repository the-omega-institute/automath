import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped ArithmeticFunction.Moebius

/-- Concrete finite-divisor data for a Ramanujan layer `Pi` and its primitive component. -/
structure conclusion_primitive_ramanujan_divisor_exact_tomography_data where
  Pi : ℕ → ℤ
  primitive : ℕ → ℤ

namespace conclusion_primitive_ramanujan_divisor_exact_tomography_data

/-- The divisor-filter identity: the visible Ramanujan layer is the sum of primitive divisor
layers. -/
def ramanujan_divisor_identity
    (D : conclusion_primitive_ramanujan_divisor_exact_tomography_data) : Prop :=
  ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, D.primitive d) = D.Pi n

/-- The primitive-layer formula records the same finite divisor expansion in layer notation. -/
def primitive_layer_formula
    (D : conclusion_primitive_ramanujan_divisor_exact_tomography_data) : Prop :=
  ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, D.primitive d) = D.Pi n

/-- Möbius inversion recovers each primitive layer from the visible divisor layers. -/
def mobius_inversion_formula
    (D : conclusion_primitive_ramanujan_divisor_exact_tomography_data) : Prop :=
  ∀ n : ℕ, 0 < n →
    (∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.fst : ℤ) * D.Pi x.snd) =
      D.primitive n

end conclusion_primitive_ramanujan_divisor_exact_tomography_data

/-- Paper label: `thm:conclusion-primitive-ramanujan-divisor-exact-tomography`. -/
theorem paper_conclusion_primitive_ramanujan_divisor_exact_tomography
    (D : conclusion_primitive_ramanujan_divisor_exact_tomography_data) :
    D.ramanujan_divisor_identity -> D.primitive_layer_formula ∧ D.mobius_inversion_formula := by
  intro hdivisor
  exact ⟨hdivisor, (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hdivisor)⟩

end Omega.Conclusion
