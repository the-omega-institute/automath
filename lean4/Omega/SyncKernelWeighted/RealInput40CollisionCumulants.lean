import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40InputMemoryMarginal
import Omega.Zeta.ArityCollisionQuadraticClosed

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The first collision cumulant at `θ = 0`, read off from the explicit memory-`11` marginal. -/
def real_input_40_collision_cumulants_first_derivative : ℝ :=
  realInput40DigitMarginal 2

/-- The second collision cumulant at `θ = 0`, identified with the quadratic pressure coefficient
already packaged in the pure-collision cubic model. -/
def real_input_40_collision_cumulants_second_derivative : ℝ :=
  Omega.Zeta.arityCollisionP2

/-- Closed forms for the first two real-input-40 collision cumulants. -/
def real_input_40_collision_cumulants_statement : Prop :=
  Omega.Zeta.arityCollisionPerronRoot = goldenRatio ^ 2 ∧
    real_input_40_collision_cumulants_first_derivative = (3 - Real.sqrt 5) / 10 ∧
    real_input_40_collision_cumulants_second_derivative = (6 * Real.sqrt 5 - 5) / 125

/-- Paper label: `cor:real-input-40-collision-cumulants`. -/
theorem paper_real_input_40_collision_cumulants :
    real_input_40_collision_cumulants_statement := by
  rcases paper_real_input_40_input_memory_marginal with
    ⟨_, _, _, _, _, _, _, _, xi_real_input_40_collision_cumulants_digit2⟩
  refine ⟨?_, ?_, ?_⟩
  · have xi_real_input_40_collision_cumulants_sqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      rw [Real.sq_sqrt]
      positivity
    unfold Omega.Zeta.arityCollisionPerronRoot goldenRatio
    ring_nf
    nlinarith [xi_real_input_40_collision_cumulants_sqrt_sq]
  · simpa [real_input_40_collision_cumulants_first_derivative] using
      xi_real_input_40_collision_cumulants_digit2
  · simpa [real_input_40_collision_cumulants_second_derivative] using
      Omega.Zeta.paper_arity_collision_quadratic_closed.2.1

end

end Omega.SyncKernelWeighted
