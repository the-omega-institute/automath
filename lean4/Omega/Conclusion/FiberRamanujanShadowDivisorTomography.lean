import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped ArithmeticFunction.Moebius BigOperators

/-- The fiberwise Ramanujan shadow obtained by summing the Möbius weights of the divisor
conditions `e ∣ d x` over the finite fiber multiset. -/
def conclusion_fiber_ramanujan_shadow_divisor_tomography_ramanujan_shadow {X : Type} [Fintype X]
    (d : X → Nat) (r : Nat) : Int :=
  ∑ x, ∑ e ∈ r.divisors.filter (fun e => e ∣ d x), (ArithmeticFunction.moebius e : Int)

/-- The divisor-count observable on the finite fiber multiset. -/
def conclusion_fiber_ramanujan_shadow_divisor_tomography_divisor_count {X : Type} [Fintype X]
    (d : X → Nat) (e : Nat) : Int :=
  ∑ x, (if e ∣ d x then (1 : Int) else 0)

/-- Finite divisor tomography for the Ramanujan shadow: exchanging the divisor sum and the fiber
sum expresses the shadow as a Möbius-weighted divisor count. -/
def conclusion_fiber_ramanujan_shadow_divisor_tomography_statement {X : Type} [Fintype X]
    (d : X → Nat) (r : Nat) : Prop :=
  conclusion_fiber_ramanujan_shadow_divisor_tomography_ramanujan_shadow d r =
    ∑ e ∈ r.divisors,
      (ArithmeticFunction.moebius e : Int) *
        conclusion_fiber_ramanujan_shadow_divisor_tomography_divisor_count d e

/-- Paper label: `thm:conclusion-fiber-ramanujan-shadow-divisor-tomography`. -/
theorem paper_conclusion_fiber_ramanujan_shadow_divisor_tomography {X : Type} [Fintype X]
    (d : X → Nat) (r : Nat) : conclusion_fiber_ramanujan_shadow_divisor_tomography_statement d r := by
  classical
  unfold conclusion_fiber_ramanujan_shadow_divisor_tomography_statement
    conclusion_fiber_ramanujan_shadow_divisor_tomography_ramanujan_shadow
    conclusion_fiber_ramanujan_shadow_divisor_tomography_divisor_count
  calc
    ∑ x, ∑ e ∈ r.divisors.filter (fun e => e ∣ d x), (ArithmeticFunction.moebius e : Int)
        =
      ∑ x, ∑ e ∈ r.divisors, (if e ∣ d x then (ArithmeticFunction.moebius e : Int) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Finset.sum_filter]
    _ = ∑ e ∈ r.divisors, ∑ x, (if e ∣ d x then (ArithmeticFunction.moebius e : Int) else 0) := by
          rw [Finset.sum_comm]
    _ =
        ∑ e ∈ r.divisors,
          (ArithmeticFunction.moebius e : Int) * ∑ x, (if e ∣ d x then (1 : Int) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          calc
            ∑ x, (if e ∣ d x then (ArithmeticFunction.moebius e : Int) else 0)
                =
              ∑ x, (ArithmeticFunction.moebius e : Int) * (if e ∣ d x then (1 : Int) else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  by_cases hdiv : e ∣ d x <;> simp [hdiv]
            _ = (ArithmeticFunction.moebius e : Int) * ∑ x, (if e ∣ d x then (1 : Int) else 0) := by
                  rw [Finset.mul_sum]

end Omega.Conclusion
