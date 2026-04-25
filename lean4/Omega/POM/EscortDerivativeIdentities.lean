import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `prop:pom-escort-derivative-identities`. The finite escort partition weights
are positive exponentials, so the second logarithmic derivative is the corresponding weighted
variance, nonnegative by finite Cauchy--Schwarz. -/
theorem paper_pom_escort_derivative_identities {X : Type*} [Fintype X] (d : X → ℝ) (q : ℝ)
    (Z : ℝ) (hZ : Z = ∑ x, Real.exp (q * d x)) (hZpos : 0 < Z) :
    0 ≤ ((∑ x, d x ^ 2 * Real.exp (q * d x)) / Z) -
      ((∑ x, d x * Real.exp (q * d x)) / Z) ^ 2 := by
  classical
  let w : X → ℝ := fun x => Real.exp (q * d x)
  let A : ℝ := ∑ x, d x ^ 2 * w x
  let B : ℝ := ∑ x, d x * w x
  have hw_nonneg : ∀ x, 0 ≤ w x := fun x => (Real.exp_pos _).le
  have hZsum : Z = ∑ x, w x := by
    simpa [w] using hZ
  have hcsRaw :
      (∑ x, d x * w x) ^ 2 ≤ (∑ x, d x ^ 2 * w x) * ∑ x, w x := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ)
      (r := fun x => d x * w x) (f := fun x => d x ^ 2 * w x) (g := fun x => w x) ?_ ?_ ?_
    · intro x _hx
      exact mul_nonneg (sq_nonneg (d x)) (hw_nonneg x)
    · intro x _hx
      exact hw_nonneg x
    · intro x _hx
      ring
  have hcs : B ^ 2 ≤ A * Z := by
    dsimp [A, B]
    rw [hZsum]
    exact hcsRaw
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hZsq_pos : 0 < Z ^ 2 := sq_pos_of_ne_zero hZne
  have hscaled : 0 ≤ Z ^ 2 * (A / Z - (B / Z) ^ 2) := by
    field_simp [hZne]
    ring_nf
    nlinarith [hcs]
  have hvariance : 0 ≤ A / Z - (B / Z) ^ 2 :=
    nonneg_of_mul_nonneg_right hscaled hZsq_pos
  simpa [A, B, w] using hvariance

end Omega.POM
