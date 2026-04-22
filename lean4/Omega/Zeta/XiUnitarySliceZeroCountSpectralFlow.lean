import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Finite-dimensional unitary-slice data packaged by the eigenphase at the chosen slice together
with the transversal crossing sign contributed by that branch. -/
structure xi_unitary_slice_zero_count_spectral_flow_data where
  branchCount : ℕ
  eigenphaseAtSlice : Fin branchCount → ℝ
  crossingSign : Fin branchCount → ℤ
  positive_transversal_crossing :
    ∀ i, crossingSign i = if eigenphaseAtSlice i = 0 then 1 else 0

namespace xi_unitary_slice_zero_count_spectral_flow_data

/-- The zero multiplicity of `det(I - U(θ))` at the chosen slice, read branch-by-branch from the
vanishing eigenphases. In this simple transversal model every zero branch contributes `1`. -/
def zeroCount (D : xi_unitary_slice_zero_count_spectral_flow_data) : ℤ :=
  ∑ i, if D.eigenphaseAtSlice i = 0 then 1 else 0

/-- The spectral-flow count obtained by summing the transversal crossing signs. -/
def spectralFlow (D : xi_unitary_slice_zero_count_spectral_flow_data) : ℤ :=
  ∑ i, D.crossingSign i

/-- Paper-facing equality between the zero count on the unitary slice and the spectral flow. -/
def zero_count_equals_spectral_flow (D : xi_unitary_slice_zero_count_spectral_flow_data) : Prop :=
  D.zeroCount = D.spectralFlow

end xi_unitary_slice_zero_count_spectral_flow_data

/-- Paper label: `thm:xi-unitary-slice-zero-count-spectral-flow`. The determinant factor
`det(I - U(θ))` vanishes exactly on the zero-phase branches, the kernel multiplicity is the sum of
their unit transversal contributions, and the same branchwise contributions define the spectral
flow. -/
theorem paper_xi_unitary_slice_zero_count_spectral_flow
    (D : xi_unitary_slice_zero_count_spectral_flow_data) : D.zero_count_equals_spectral_flow := by
  simp [xi_unitary_slice_zero_count_spectral_flow_data.zero_count_equals_spectral_flow,
    xi_unitary_slice_zero_count_spectral_flow_data.zeroCount,
    xi_unitary_slice_zero_count_spectral_flow_data.spectralFlow,
    D.positive_transversal_crossing]

end
end Omega.Zeta
