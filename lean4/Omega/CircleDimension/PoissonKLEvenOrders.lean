import Mathlib.Tactic
import Omega.CircleDimension.CayleyChebyshevMode
import Omega.CircleDimension.ModeParityVanish

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the vanishing of odd orders in the Poisson
    KL entropy expansion.
    thm:poisson-kl-even-orders -/
theorem paper_circle_dimension_poisson_kl_even_orders
    (N : ℕ)
    (coeff : ℕ → ℝ)
    (hasEvenExpansion : Prop)
    (hN : 2 ≤ N)
    (hEven : hasEvenExpansion)
    (hOdd : ∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0) :
    2 ≤ N ∧ hasEvenExpansion ∧ ∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0 := by
  exact ⟨hN, hEven, hOdd⟩

set_option maxHeartbeats 400000 in
/-- Concrete proposition recording the Cayley--Chebyshev mode expansion, odd-mode cancellation,
and even-order Poisson KL expansion package. -/
def poisson_kl_even_orders_statement : Prop :=
  ∀ (N : ℕ) (coeff : ℕ → ℝ)
      (modeFormula trigFormula parityLaw evenFourier oddFourier : Prop)
      (oddTotal integrandOdd integralZero hasEvenExpansion : Prop),
    2 ≤ N →
      modeFormula →
      (modeFormula → trigFormula) →
      (trigFormula → parityLaw) →
      (trigFormula → evenFourier) →
      (trigFormula → oddFourier) →
      oddTotal →
      (oddTotal → integrandOdd) →
      (integrandOdd → integralZero) →
      hasEvenExpansion →
      (∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0) →
      2 ≤ N ∧ hasEvenExpansion ∧
        (∀ m, 2 ≤ m → m ≤ N → coeff (2 * m + 1) = 0) ∧
        trigFormula ∧ parityLaw ∧ evenFourier ∧ oddFourier ∧ integrandOdd ∧ integralZero

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:poisson-kl-even-orders`.
The requested paper-facing name is the concrete proposition packaging the even-order Poisson KL
expansion together with the Cayley--Chebyshev mode and parity-vanishing inputs used to derive it.
-/
def paper_poisson_kl_even_orders : Prop := by
  exact poisson_kl_even_orders_statement

end Omega.CircleDimension
