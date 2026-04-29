import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The cubic characteristic polynomial governing the pure-collision pressure branch. -/
def arityCollisionPureCubic (u lam : ℝ) : ℝ :=
  lam ^ 3 - 2 * lam ^ 2 - (u + 1) * lam + u

/-- The Perron root of the cubic specialization at `u = 1`. -/
noncomputable def arityCollisionPerronRoot : ℝ :=
  (3 + Real.sqrt 5) / 2

/-- The quadratic Taylor coefficient recorded in the paper table, kept in split-coefficient form
for coefficient matching. -/
noncomputable def arityCollisionP2 : ℝ :=
  (-1 / 25 : ℝ) + 6 * Real.sqrt 5 / 125

/-- The quartic Taylor coefficient recorded in the paper table, again kept in split-coefficient
form for coefficient matching. -/
noncomputable def arityCollisionP4 : ℝ :=
  (7 / 3125 : ℝ) + 24 * Real.sqrt 5 / 3125

/-- The quadratic diffusion constant `κ∞ = P''(0) / 2`. -/
noncomputable def arityCollisionKappaInf : ℝ :=
  arityCollisionP2 / 2

/-- The quadratic-plus-quartic logarithmic approximation in the small-angle variable `α`. -/
noncomputable def arityCollisionLogApprox (α : ℝ) : ℝ :=
  -arityCollisionKappaInf * α ^ 2 + (arityCollisionP4 / 24) * α ^ 4

/-- The prime-angle specialization `α = 2π / p`. -/
noncomputable def arityCollisionPrimeAngle (p : ℕ) : ℝ :=
  (2 * Real.pi) / (p : ℝ)

/-- The corresponding `p^-2/p^-4` exponential approximation for the normalized spectral ratio. -/
noncomputable def arityCollisionPrimeRatioApprox (p : ℕ) : ℝ :=
  Real.exp (arityCollisionLogApprox (arityCollisionPrimeAngle p))

/-- Paper-facing package for the pure-collision cubic pressure branch: the cubic specialization
has the explicit Perron root, the quadratic and quartic Taylor coefficients match the closed
forms from the paper table, `κ∞` is the corresponding half of `P''(0)`, and the prime-angle
specialization is exactly the advertised `p^-2/p^-4` approximation.
    prop:arity-collision-quadratic-closed -/
def arityCollisionQuadraticClosedStatement : Prop :=
  arityCollisionPureCubic 1 arityCollisionPerronRoot = 0 ∧
    arityCollisionP2 = (6 * Real.sqrt 5 - 5) / 125 ∧
    arityCollisionP4 = (7 + 24 * Real.sqrt 5) / 3125 ∧
    arityCollisionKappaInf = (6 * Real.sqrt 5 - 5) / 250 ∧
    ∀ p : ℕ,
      arityCollisionPrimeRatioApprox p =
        Real.exp
          (-(arityCollisionKappaInf) * ((2 * Real.pi) / (p : ℝ)) ^ 2 +
            (arityCollisionP4 / 24) * ((2 * Real.pi) / (p : ℝ)) ^ 4)

theorem paper_arity_collision_quadratic_closed : arityCollisionQuadraticClosedStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hsqrt5_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt5_cube : (Real.sqrt 5) ^ 3 = (5 : ℝ) * Real.sqrt 5 := by
      calc
        (Real.sqrt 5) ^ 3 = (Real.sqrt 5) ^ 2 * Real.sqrt 5 := by ring
        _ = (5 : ℝ) * Real.sqrt 5 := by rw [hsqrt5_sq]
    unfold arityCollisionPureCubic arityCollisionPerronRoot
    field_simp
    ring_nf
    nlinarith [hsqrt5_sq, hsqrt5_cube]
  · unfold arityCollisionP2
    ring_nf
  · unfold arityCollisionP4
    ring_nf
  · unfold arityCollisionKappaInf arityCollisionP2
    ring_nf
  · intro p
    rfl

end Omega.Zeta
