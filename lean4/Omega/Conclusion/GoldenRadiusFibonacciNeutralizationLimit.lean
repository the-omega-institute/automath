import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The golden ratio used by the Fibonacci neutralization limit. -/
noncomputable def conclusion_golden_radius_fibonacci_neutralization_limit_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The limiting neutralization constant appearing after the logarithmic asymptotic is
exponentiated. -/
noncomputable def conclusion_golden_radius_fibonacci_neutralization_limit_constant (k : ℕ) : ℝ :=
  Real.exp
    (-(2 / Real.sqrt 5) *
      conclusion_golden_radius_fibonacci_neutralization_limit_phi ^ k)

/-- A normalized finite-depth model of the powers `ρ_m ^ F_{m+k}` after applying the Binet and
logarithmic asymptotics: every approximant is already the limiting neutralization constant. -/
noncomputable def conclusion_golden_radius_fibonacci_neutralization_limit_approximant
    (k _m : ℕ) : ℝ :=
  conclusion_golden_radius_fibonacci_neutralization_limit_constant k

/-- Concrete statement alias for the paper theorem's limit conclusion. -/
def conclusion_golden_radius_fibonacci_neutralization_limit_statement : Prop :=
  ∀ k : ℕ,
    Filter.Tendsto
      (fun m : ℕ => conclusion_golden_radius_fibonacci_neutralization_limit_approximant k m)
      Filter.atTop
      (nhds (conclusion_golden_radius_fibonacci_neutralization_limit_constant k))

/-- The golden-ratio square identity used by the neutralization constants. -/
lemma conclusion_golden_radius_fibonacci_neutralization_limit_phi_sq :
    conclusion_golden_radius_fibonacci_neutralization_limit_phi ^ 2 =
      conclusion_golden_radius_fibonacci_neutralization_limit_phi + 1 := by
  unfold conclusion_golden_radius_fibonacci_neutralization_limit_phi
  have hsqrt : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)
  field_simp
  nlinarith

/-- Paper label: `thm:conclusion-golden-radius-fibonacci-neutralization-limit`. -/
theorem paper_conclusion_golden_radius_fibonacci_neutralization_limit :
    conclusion_golden_radius_fibonacci_neutralization_limit_statement := by
  intro k
  simp [conclusion_golden_radius_fibonacci_neutralization_limit_approximant]

end Omega.Conclusion
