import Mathlib.Tactic
import Omega.Zeta.XiEndpointAbsorptionKernelRepresentation

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Denominator of the single-node endpoint absorption kernel. -/
def xi_endpoint_absorption_jet_moments_den (gamma delta r : Real) : Real :=
  ((1 - r) * gamma) ^ 2 + (1 + delta + r * (1 - delta)) ^ 2

/-- The first derivative of the denominator at `r = 1`. -/
def xi_endpoint_absorption_jet_moments_den_deriv_at_one (_gamma delta : Real) : Real :=
  4 * (1 - delta)

/-- The second derivative of the denominator at `r = 1`. -/
def xi_endpoint_absorption_jet_moments_den_second_at_one (gamma delta : Real) : Real :=
  2 * gamma ^ 2 + 2 * (1 - delta) ^ 2

/-- Algebraic first endpoint jet of one absorption node. -/
def xi_endpoint_absorption_jet_moments_first_node (gamma delta : Real) : Real :=
  -(4 * delta) * xi_endpoint_absorption_jet_moments_den_deriv_at_one gamma delta /
    (xi_endpoint_absorption_jet_moments_den gamma delta 1) ^ 2

/-- Algebraic second endpoint jet of one absorption node. -/
def xi_endpoint_absorption_jet_moments_second_node (gamma delta : Real) : Real :=
  (4 * delta) *
    (2 * (xi_endpoint_absorption_jet_moments_den_deriv_at_one gamma delta) ^ 2 /
        (xi_endpoint_absorption_jet_moments_den gamma delta 1) ^ 3 -
      xi_endpoint_absorption_jet_moments_den_second_at_one gamma delta /
        (xi_endpoint_absorption_jet_moments_den gamma delta 1) ^ 2)

/-- Endpoint value and first two algebraic jets of the finite absorption profile. -/
def xi_endpoint_absorption_jet_moments_statement (D : XiEndpointAbsorptionData) : Prop :=
  D.profile 1 = ∑ k, D.delta k ∧
    (∑ k, xi_endpoint_absorption_jet_moments_first_node (D.gamma k) (D.delta k)) =
      ∑ k, D.delta k * (D.delta k - 1) ∧
    (∑ k, xi_endpoint_absorption_jet_moments_second_node (D.gamma k) (D.delta k)) =
      ∑ k, (1 / 2 : Real) * D.delta k *
        (3 * (D.delta k - 1) ^ 2 - (D.gamma k) ^ 2)

private lemma xi_endpoint_absorption_jet_moments_node_value (gamma delta : Real) :
    xiEndpointSingleNodeProfile gamma delta 1 = delta := by
  unfold xiEndpointSingleNodeProfile
  ring_nf

private lemma xi_endpoint_absorption_jet_moments_first_node_eq (gamma delta : Real) :
    xi_endpoint_absorption_jet_moments_first_node gamma delta = delta * (delta - 1) := by
  unfold xi_endpoint_absorption_jet_moments_first_node
    xi_endpoint_absorption_jet_moments_den
    xi_endpoint_absorption_jet_moments_den_deriv_at_one
  ring_nf

private lemma xi_endpoint_absorption_jet_moments_second_node_eq (gamma delta : Real) :
    xi_endpoint_absorption_jet_moments_second_node gamma delta =
      (1 / 2 : Real) * delta * (3 * (delta - 1) ^ 2 - gamma ^ 2) := by
  unfold xi_endpoint_absorption_jet_moments_second_node
    xi_endpoint_absorption_jet_moments_den
    xi_endpoint_absorption_jet_moments_den_deriv_at_one
    xi_endpoint_absorption_jet_moments_den_second_at_one
  ring_nf

/-- Paper label: `thm:xi-endpoint-absorption-jet-moments`. -/
theorem paper_xi_endpoint_absorption_jet_moments (D : Omega.Zeta.XiEndpointAbsorptionData) :
    xi_endpoint_absorption_jet_moments_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · unfold XiEndpointAbsorptionData.profile
    refine Finset.sum_congr rfl ?_
    intro k _
    exact xi_endpoint_absorption_jet_moments_node_value (D.gamma k) (D.delta k)
  · refine Finset.sum_congr rfl ?_
    intro k _
    exact xi_endpoint_absorption_jet_moments_first_node_eq (D.gamma k) (D.delta k)
  · refine Finset.sum_congr rfl ?_
    intro k _
    exact xi_endpoint_absorption_jet_moments_second_node_eq (D.gamma k) (D.delta k)

end

end Omega.Zeta
