import Omega.Conclusion.PrimeRegisterEllipseCompleteEquivalence

namespace Omega.Zeta

/-- Concrete two-axis positive-integer data for the integer-axis ellipse prime-axis rigidity
package. The first axis is the integer axis and the second is the ellipse prime axis. -/
abbrev xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data := ℕ+ × ℕ+

namespace xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data

/-- The integer axis of the two-axis ellipse monoid. -/
def integerAxis (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) : ℕ+ :=
  D.1

/-- The prime axis of the two-axis ellipse monoid. -/
def ellipsePrimeAxis (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) : ℕ+ :=
  D.2

/-- The product register obtained by multiplying the two positive-integer prime registers. -/
def primeAxisProductRegister
    (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) :
    Omega.Conclusion.PrimeRegisterVector :=
  Omega.Conclusion.primeRegisterMul
    (Omega.Conclusion.primeRegisterOfPNat D.integerAxis)
    (Omega.Conclusion.primeRegisterOfPNat D.ellipsePrimeAxis)

/-- Unique factorization transports the two positive-integer axes to the product register. -/
def freeProductDecomposition
    (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) : Prop :=
  Omega.Conclusion.primeRegisterNorm D.primeAxisProductRegister =
    D.integerAxis * D.ellipsePrimeAxis

/-- Prime-axis exponents determine a register by finite-support extensionality. -/
def homDeterminedByPrimeAxes
    (_D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) : Prop :=
  ∀ r s : Omega.Conclusion.PrimeRegisterVector,
    (∀ p : ℕ, (r : ℕ →₀ ℕ) p = (s : ℕ →₀ ℕ) p) -> r = s

/-- The real-valued valuation of the product register is the product of the two axes. -/
def realValuedValuationFormula
    (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) : Prop :=
  ((Omega.Conclusion.primeRegisterNorm D.primeAxisProductRegister : ℕ) : ℝ) =
    ((D.integerAxis : ℕ) : ℝ) * ((D.ellipsePrimeAxis : ℕ) : ℝ)

end xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data

/-- Paper label: `prop:xi-time-part63b-integer-axis-ellipse-prime-axis-rigidity`. -/
theorem paper_xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity
    (D : xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data) :
    D.freeProductDecomposition ∧ D.homDeterminedByPrimeAxes ∧ D.realValuedValuationFormula := by
  refine ⟨?_, ?_, ?_⟩
  · simp [
      xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data.freeProductDecomposition,
      xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data.primeAxisProductRegister,
      Omega.Conclusion.primeRegisterMul,
      Omega.Conclusion.primeRegisterNorm,
      Omega.Conclusion.primeRegisterOfPNat]
  · intro r s h
    exact Subtype.ext (Finsupp.ext h)
  · have hProduct : D.freeProductDecomposition := by
      simp [
        xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data.freeProductDecomposition,
        xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data.primeAxisProductRegister,
        Omega.Conclusion.primeRegisterMul,
        Omega.Conclusion.primeRegisterNorm,
        Omega.Conclusion.primeRegisterOfPNat]
    simpa [
      xi_time_part63b_integer_axis_ellipse_prime_axis_rigidity_data.realValuedValuationFormula]
      using congrArg (fun n : ℕ+ => ((n : ℕ) : ℝ)) hProduct

end Omega.Zeta
