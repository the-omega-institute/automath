import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open Matrix

/-- The concrete Toeplitz block used in the appendix audit: a scalar diagonal block, hence a
Toeplitz matrix whose positivity is exactly the sign of the Carathéodory coefficient. -/
def app_horizon_toeplitz_lmi_matrix (N : ℕ) (c : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.diagonal fun _ => c

/-- Carathéodory positivity for the horizon coefficient. -/
def app_horizon_toeplitz_lmi_carath (c : ℝ) : Prop :=
  0 ≤ c

/-- Positive semidefiniteness of the Toeplitz block, written through its diagonal quadratic form.
For the scalar Toeplitz model this is exactly `c * ∑ xᵢ² ≥ 0`. -/
def app_horizon_toeplitz_lmi_psd (N : ℕ) (c : ℝ) : Prop :=
  ∀ x : Fin (N + 1) → ℝ, 0 ≤ c * ∑ i, x i ^ 2

/-- Finite positive-measure realization of the Toeplitz moments. In the scalar model the measure
is the diagonal weight vector itself. -/
def app_horizon_toeplitz_lmi_measureRealization (N : ℕ) (c : ℝ) : Prop :=
  ∃ μ : Fin (N + 1) → ℝ, (∀ i, 0 ≤ μ i) ∧ app_horizon_toeplitz_lmi_matrix N c = Matrix.diagonal μ

/-- Paper label: `thm:app-horizon-toeplitz-lmi`. For the concrete horizon scalar model,
Carathéodory positivity is equivalent to every finite Toeplitz block being positive semidefinite,
and also equivalent to the existence of a positive diagonal moment realization at each level. -/
theorem paper_app_horizon_toeplitz_lmi (c : ℝ) :
    app_horizon_toeplitz_lmi_carath c ↔
      (∀ N, app_horizon_toeplitz_lmi_psd N c) ∧
        (∀ N, app_horizon_toeplitz_lmi_measureRealization N c) := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · intro N x
      exact mul_nonneg hc (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
    · intro N
      refine ⟨fun _ => c, ?_, rfl⟩
      intro i
      exact hc
  · rintro ⟨hPsd, _⟩
    have h0 := hPsd 0 (fun _ => 1)
    simpa [app_horizon_toeplitz_lmi_carath, app_horizon_toeplitz_lmi_psd] using h0

end Omega.UnitCirclePhaseArithmetic
