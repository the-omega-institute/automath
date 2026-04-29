import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite positive Hausdorff moment data for the endpoint probe. -/
structure xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data where
  order : ℕ
  mass : Fin (order + 1) → ℝ
  point : Fin (order + 1) → ℝ
  mass_nonneg : ∀ i, 0 ≤ mass i
  point_nonneg : ∀ i, 0 ≤ point i
  point_le_one : ∀ i, point i ≤ 1

/-- Endpoint-probe moments of the finite positive measure on `[0, 1]`. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_moment
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) (n : ℕ) :
    ℝ :=
  ∑ i, D.mass i * D.point i ^ n

/-- The positive finite-difference kernel for Hausdorff complete monotonicity. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_difference
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data)
    (n k : ℕ) : ℝ :=
  ∑ i, D.mass i * D.point i ^ n * (1 - D.point i) ^ k

/-- The endpoint atom mass isolated by the Bochner/Hausdorff probe. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_endpointAtom
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) : ℝ :=
  Finset.sum (Finset.univ.filter (fun i => D.point i = 1)) fun i => D.mass i

/-- The finite pushforward representation of all endpoint-probe moments. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_hausdorffRepresentation
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) : Prop :=
  ∀ n : ℕ,
    xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_moment D n =
      ∑ i, D.mass i * D.point i ^ n

/-- Complete monotonicity of the finite positive Hausdorff moment sequence. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_completeMonotone
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) : Prop :=
  ∀ n k : ℕ,
    0 ≤ xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_difference D n k

/-- Concrete paper-facing endpoint-probe statement. -/
def xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_statement
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) : Prop :=
  xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_hausdorffRepresentation D ∧
    xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_endpointAtom D =
      Finset.sum (Finset.univ.filter (fun i => D.point i = 1)) (fun i => D.mass i) ∧
    xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_completeMonotone D

/-- Paper label:
`thm:xi-operator-endpoint-probe-hausdorff-bochner-complete-monotone`. -/
theorem paper_xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone
    (D : xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_data) :
    xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_statement D := by
  refine ⟨?_, rfl, ?_⟩
  · intro n
    rfl
  · intro n k
    unfold xi_operator_endpoint_probe_hausdorff_bochner_complete_monotone_difference
    refine Finset.sum_nonneg fun i _hi => ?_
    exact mul_nonneg (mul_nonneg (D.mass_nonneg i) (pow_nonneg (D.point_nonneg i) n))
      (pow_nonneg (sub_nonneg.mpr (D.point_le_one i)) k)

end

end Omega.Zeta
