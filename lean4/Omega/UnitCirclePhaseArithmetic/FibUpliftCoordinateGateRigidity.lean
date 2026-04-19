import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial

namespace Omega.UnitCirclePhaseArithmetic

/-- Concrete uplift data for a single coordinate `u`: a gate `g`, a residual term `R`, and the
Fibonacci-polynomial functional equation evaluated at that coordinate. -/
structure FibUpliftCoordinateGateRigiditySystem where
  u : ℤ
  g : ℤ → ℤ
  R : ℤ → ℤ
  u_ne_zero : u ≠ 0
  fibFunctionalEquation :
    ∀ n : ℕ, g u * (Omega.fibPoly n).eval u + R u =
      (1 + u) * (Omega.fibPoly n).eval u + (1 - u)

def gIsOnePlusU (S : FibUpliftCoordinateGateRigiditySystem) : Prop :=
  S.g S.u = 1 + S.u

def rIsLeeYangGate (S : FibUpliftCoordinateGateRigiditySystem) : Prop :=
  S.R S.u = 1 - S.u

/-- Evaluating the uplift functional equation at `n = 2` and `n = 3`, together with the
Fibonacci-polynomial identities `F₂ = 1` and `F₃ = 1 + X`, forces the gate to be `1 + u` and
the residual term to be the Lee--Yang gate `1 - u`.
    thm:fib-uplift-coordinate-gate-rigidity -/
theorem paper_fib_uplift_coordinate_gate_rigidity (S : FibUpliftCoordinateGateRigiditySystem) :
    gIsOnePlusU S ∧ rIsLeeYangGate S := by
  have h2 : S.g S.u + S.R S.u = 2 := by
    simpa [Omega.fibPoly_two] using S.fibFunctionalEquation 2
  have h3 :
      S.g S.u * (1 + S.u) + S.R S.u = (1 + S.u) * (1 + S.u) + (1 - S.u) := by
    simpa [Omega.fibPoly_three] using S.fibFunctionalEquation 3
  have hR : S.R S.u = 2 - S.g S.u := by
    omega
  have hmul : S.g S.u * S.u = (1 + S.u) * S.u := by
    rw [hR] at h3
    nlinarith
  have hg : gIsOnePlusU S := by
    unfold gIsOnePlusU
    apply mul_right_cancel₀ S.u_ne_zero
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hRfinal : rIsLeeYangGate S := by
    unfold rIsLeeYangGate
    unfold gIsOnePlusU at hg
    omega
  exact ⟨hg, hRfinal⟩

end Omega.UnitCirclePhaseArithmetic
