import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.Rank2RigidityFibonacciFusionLaw

namespace Omega.Conclusion

/-- Concrete rank-two reverse-Fibonacci fusion data.  The natural numbers `a` and `b` encode
`X ⊗ X = a·1 + b·X`, while `u n` records the vacuum multiplicity in `X^⊗n`. -/
structure conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data where
  a : ℕ
  b : ℕ
  u : ℕ → ℕ
  u_one : u 1 = 0
  u_two : u 2 = 1
  multiplicity_recurrence :
    ∀ n, 1 ≤ n → u (n + 2) = a * u n + b * u (n + 1)
  fibonacci_dimensions :
    ∀ n, 1 ≤ n → u n = Nat.fib (n - 1)

namespace conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data

/-- The rank-two fusion law forced by the Fibonacci multiplicities. -/
def fusion_law
    (D : conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data) :
    Prop :=
  D.a = 1 ∧ D.b = 1

/-- The Frobenius--Perron dimension is the positive golden root of `x^2 = x + 1`. -/
def fp_dimension_phi
    (D : conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data) :
    Prop :=
  Real.goldenRatio ^ 2 = (D.a : ℝ) + (D.b : ℝ) * Real.goldenRatio

end conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data

/-- Paper label:
`thm:conclusion-single-component-fiber-reverse-fibonacci-fusion-rigidity`. -/
theorem paper_conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity
    (D : conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data) :
    D.fusion_law ∧ D.fp_dimension_phi := by
  have hrigid :
      D.a = 1 ∧ D.b = 1 :=
    Omega.POM.paper_pom_rank2_rigidity_fibonacci_fusion_law D.a D.b D.u D.u_one D.u_two
      D.multiplicity_recurrence D.fibonacci_dimensions
  refine ⟨hrigid, ?_⟩
  rcases hrigid with ⟨ha, hb⟩
  simp [conclusion_single_component_fiber_reverse_fibonacci_fusion_rigidity_data.fp_dimension_phi,
    ha, hb, Real.goldenRatio_sq, add_comm]

end Omega.Conclusion
