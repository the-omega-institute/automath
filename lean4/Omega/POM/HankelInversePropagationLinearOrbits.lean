import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete data for the inverse-propagation package attached to a shifted Hankel family. -/
structure POMHankelInversePropagationLinearOrbitData where
  d : ℕ
  k0 : ℕ
  H : ℕ → Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  b : Fin d → ℝ
  obs : (Fin d → ℝ) → ℝ
  state : ℕ → Fin d → ℝ
  obsSeq : ℕ → ℝ
  recurrenceOrder : ℕ
  recurrenceCoeffs : Fin recurrenceOrder → ℝ
  hA_det : IsUnit A.det
  hshift : ∀ r, H (k0 + r) = H k0 * A ^ r
  hstate : ∀ r, state r = (H (k0 + r))⁻¹.mulVec b
  hobsSeq : ∀ r, obsSeq r = obs (state r)
  hrecurrenceOrder_le : recurrenceOrder ≤ d
  hrecurrence :
    ∀ r, obsSeq (r + recurrenceOrder) = ∑ i, recurrenceCoeffs i * obsSeq (r + i)

/-- Publication-facing package for inverse Hankel propagation, linear solution orbits, and the
resulting finite-order scalar recurrence. -/
def POMHankelInversePropagationLinearOrbitData.package
    (D : POMHankelInversePropagationLinearOrbitData) : Prop :=
  (∀ r, (D.H (D.k0 + r))⁻¹ = D.A⁻¹ ^ r * (D.H D.k0)⁻¹) ∧
    (∀ r, D.state r = (D.A⁻¹ ^ r).mulVec (D.state 0)) ∧
    (∀ r, D.obsSeq r = D.obs (D.state r)) ∧
    ∃ m ≤ D.d, ∃ coeff : Fin m → ℝ, ∀ r, D.obsSeq (r + m) = ∑ i, coeff i * D.obsSeq (r + i)

set_option maxHeartbeats 400000 in
/-- The inverse Hankel family propagates by powers of `A⁻¹`; the corresponding linear solves form
an `A⁻¹`-orbit; and any chosen scalar observation is packaged together with a finite recurrence
witness of order at most `d`.
    thm:pom-hankel-inverse-propagation-linear-orbits -/
theorem paper_pom_hankel_inverse_propagation_linear_orbits
    (D : POMHankelInversePropagationLinearOrbitData) : D.package := by
  have hInvPow : ∀ n : ℕ, (D.A ^ n)⁻¹ = D.A⁻¹ ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ, Matrix.mul_inv_rev, ih, pow_succ']
  refine ⟨?_, ?_, D.hobsSeq, ?_⟩
  · intro r
    rw [D.hshift r, Matrix.mul_inv_rev]
    rw [hInvPow r]
  · intro r
    rw [D.hstate r, D.hstate 0]
    calc
      (D.H (D.k0 + r))⁻¹.mulVec D.b
          = ((D.A⁻¹ ^ r) * (D.H D.k0)⁻¹).mulVec D.b := by
              rw [show (D.H (D.k0 + r))⁻¹ = D.A⁻¹ ^ r * (D.H D.k0)⁻¹ by
                rw [D.hshift r, Matrix.mul_inv_rev]
                rw [hInvPow r]]
      _ = (D.A⁻¹ ^ r).mulVec ((D.H D.k0)⁻¹.mulVec D.b) := by
            rw [Matrix.mulVec_mulVec]
  · exact ⟨D.recurrenceOrder, D.hrecurrenceOrder_le, D.recurrenceCoeffs, D.hrecurrence⟩

end Omega.POM
