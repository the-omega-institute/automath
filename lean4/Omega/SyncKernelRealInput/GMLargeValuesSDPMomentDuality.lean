import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.SyncKernelRealInput

/-- Concrete finite-dimensional Gram data for the large-values SDP model. -/
structure gm_large_values_sdp_moment_duality_data where
  N : ℕ
  R : ℕ
  k : ℕ
  V : ℝ
  v : Fin R → Fin N → ℝ
  v0 : Fin N → ℝ
  large_value_lower :
    ∀ r : Fin R, V ≤ |∑ n : Fin N, v r n * v0 n|

/-- The Gram block `G`. -/
def gm_large_values_sdp_moment_duality_gramEntry
    (D : gm_large_values_sdp_moment_duality_data) (r s : Fin D.R) : ℝ :=
  ∑ n : Fin D.N, D.v r n * D.v s n

/-- The coupling vector `u`. -/
def gm_large_values_sdp_moment_duality_uEntry
    (D : gm_large_values_sdp_moment_duality_data) (r : Fin D.R) : ℝ :=
  ∑ n : Fin D.N, D.v r n * D.v0 n

/-- The bottom-right scalar `M = ‖v₀‖²`. -/
def gm_large_values_sdp_moment_duality_mass
    (D : gm_large_values_sdp_moment_duality_data) : ℝ :=
  ∑ n : Fin D.N, D.v0 n ^ 2

/-- The quadratic form associated with the Gram block matrix `H = [[G,u],[uᵀ,M]]`. -/
def gm_large_values_sdp_moment_duality_blockQuadraticForm
    (D : gm_large_values_sdp_moment_duality_data) (a : Fin D.R → ℝ) (b : ℝ) : ℝ :=
  ∑ n : Fin D.N, ((∑ r : Fin D.R, a r * D.v r n) + b * D.v0 n) ^ 2

/-- Positive semidefiniteness of the block matrix, stated through its quadratic form. -/
def gm_large_values_sdp_moment_duality_blockPsd
    (D : gm_large_values_sdp_moment_duality_data) : Prop :=
  ∀ a : Fin D.R → ℝ, ∀ b : ℝ,
    0 ≤ gm_large_values_sdp_moment_duality_blockQuadraticForm D a b

/-- The Gram-model feasibility statement: the matrix data come from an explicit finite family of
vectors together with the distinguished vector `v₀`. -/
def gm_large_values_sdp_moment_duality_gramFeasible
    (D : gm_large_values_sdp_moment_duality_data) : Prop :=
  ∃ v : Fin D.R → Fin D.N → ℝ, ∃ v0 : Fin D.N → ℝ,
    (∀ r s : Fin D.R,
      gm_large_values_sdp_moment_duality_gramEntry D r s = ∑ n : Fin D.N, v r n * v s n) ∧
    (∀ r : Fin D.R,
      gm_large_values_sdp_moment_duality_uEntry D r = ∑ n : Fin D.N, v r n * v0 n) ∧
    gm_large_values_sdp_moment_duality_mass D = ∑ n : Fin D.N, v0 n ^ 2

/-- Finite trace moments extracted from the Gram block. -/
def gm_large_values_sdp_moment_duality_traceMoment
    (D : gm_large_values_sdp_moment_duality_data) (j : Fin (2 * D.k + 2)) : ℝ :=
  ∑ r : Fin D.R, (gm_large_values_sdp_moment_duality_gramEntry D r r) ^ j.1

/-- A finite SDP-style certificate: one keeps only the trace moments up to degree `2k+1`. -/
def gm_large_values_sdp_moment_duality_finiteCertificate
    (D : gm_large_values_sdp_moment_duality_data) : Prop :=
  ∃ moments : Fin (2 * D.k + 2) → ℝ,
    moments = gm_large_values_sdp_moment_duality_traceMoment D ∧ moments 0 = D.R

/-- Paper label: `thm:gm-large-values-sdp-moment-duality`. The explicit vector family gives a Gram
representation of the block matrix, hence a positive-semidefinite quadratic form; the same finite
Gram data serve as a feasible SDP witness, and the trace moments up to degree `2k+1` define the
finite certificate tracked by the large-values argument. -/
theorem paper_gm_large_values_sdp_moment_duality
    (D : gm_large_values_sdp_moment_duality_data) :
    gm_large_values_sdp_moment_duality_blockPsd D ∧
      (∀ r : Fin D.R, D.V ≤ |gm_large_values_sdp_moment_duality_uEntry D r|) ∧
      gm_large_values_sdp_moment_duality_gramFeasible D ∧
      gm_large_values_sdp_moment_duality_finiteCertificate D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    unfold gm_large_values_sdp_moment_duality_blockQuadraticForm
    exact Finset.sum_nonneg fun n _ => sq_nonneg _
  · intro r
    simpa [gm_large_values_sdp_moment_duality_uEntry] using D.large_value_lower r
  · refine ⟨D.v, D.v0, ?_, ?_, ?_⟩
    · intro r s
      rfl
    · intro r
      rfl
    · rfl
  · refine ⟨gm_large_values_sdp_moment_duality_traceMoment D, rfl, ?_⟩
    simp [gm_large_values_sdp_moment_duality_traceMoment]

end Omega.SyncKernelRealInput
