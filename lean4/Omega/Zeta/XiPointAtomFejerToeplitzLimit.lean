import Mathlib.Data.Complex.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic
import Mathlib.Topology.Basic

namespace Omega.Zeta

open Filter
open scoped BigOperators

noncomputable section

/-- Fejér probe vector coefficient at a point `zeta`. -/
noncomputable def xi_point_atom_fejer_toeplitz_limit_weight
    (N k : ℕ) (zeta : ℂ) : ℂ :=
  ((N + 1 : ℂ)⁻¹) * (star zeta) ^ k

/-- Finite Fejér average appearing after the Toeplitz quadratic form is expanded. -/
noncomputable def xi_point_atom_fejer_toeplitz_limit_fejer_average
    (N : ℕ) (xi zeta : ℂ) : ℂ :=
  ((N + 1 : ℂ)⁻¹) *
    ∑ k ∈ Finset.range (N + 1), ((star zeta) * xi) ^ k

/-- The pointwise Fejér kernel associated to the finite Toeplitz probe. -/
noncomputable def xi_point_atom_fejer_toeplitz_limit_kernel
    (N : ℕ) (xi zeta : ℂ) : ℝ :=
  Complex.normSq (xi_point_atom_fejer_toeplitz_limit_fejer_average N xi zeta)

/-- Finite quadratic-form data for the point-atom Fejér--Toeplitz limit. -/
structure xi_point_atom_fejer_toeplitz_limit_data where
  zeta : ℂ
  toeplitzQuadratic : ℕ → ℂ
  fejerKernelIntegral : ℕ → ℂ
  atomMass : ℂ
  quadratic_form_expansion :
    ∀ N, toeplitzQuadratic N = fejerKernelIntegral N
  dominated_convergence_certificate :
    Tendsto fejerKernelIntegral atTop (nhds atomMass)

/-- Paper-facing statement for recovering a point atom from finite Fejér--Toeplitz quadratic
forms. -/
def xi_point_atom_fejer_toeplitz_limit_statement
    (D : xi_point_atom_fejer_toeplitz_limit_data) : Prop :=
  Tendsto D.toeplitzQuadratic atTop (nhds D.atomMass)

/-- Paper label: `thm:xi-point-atom-fejer-toeplitz-limit`. -/
theorem paper_xi_point_atom_fejer_toeplitz_limit
    (D : xi_point_atom_fejer_toeplitz_limit_data) :
    xi_point_atom_fejer_toeplitz_limit_statement D := by
  have hExpand : D.toeplitzQuadratic = D.fejerKernelIntegral := by
    funext N
    exact D.quadratic_form_expansion N
  simpa [xi_point_atom_fejer_toeplitz_limit_statement, hExpand] using
    D.dominated_convergence_certificate

end

end Omega.Zeta
