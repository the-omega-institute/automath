import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Finite Cayley-coordinate data for a Blaschke family at the endpoint `-1`. -/
structure XiEndpointAbsorptionData where
  κ : ℕ
  gamma : Fin κ → Real
  delta : Fin κ → Real

/-- Single-node endpoint absorption kernel written in a Cayley-coordinate form. -/
noncomputable def xiEndpointSingleNodeProfile (gamma delta r : Real) : Real :=
  4 * delta / (((1 - r) * gamma) ^ 2 + (1 + delta + r * (1 - delta)) ^ 2)

/-- Finite endpoint absorption profile obtained by summing the single-node kernels. -/
noncomputable def XiEndpointAbsorptionData.profile (D : XiEndpointAbsorptionData) (r : Real) : Real :=
  ∑ k, xiEndpointSingleNodeProfile (D.gamma k) (D.delta k) r

private lemma xiEndpointSingleNodeProfile_eq_kernel (gamma delta r : Real) :
    xiEndpointSingleNodeProfile gamma delta r =
      4 * delta / ((1 - r)^2 * gamma^2 + (1 + r + (1 - r) * delta)^2) := by
  unfold xiEndpointSingleNodeProfile
  have hden :
      ((1 - r) * gamma) ^ 2 + (1 + delta + r * (1 - delta)) ^ 2 =
        (1 - r)^2 * gamma^2 + (1 + r + (1 - r) * delta)^2 := by
    ring
  rw [hden]

/-- Paper label: `thm:xi-endpoint-absorption-kernel-representation`. -/
theorem paper_xi_endpoint_absorption_kernel_representation (D : XiEndpointAbsorptionData) :
    ∀ r : Real, 0 < r → r < 1 →
      D.profile r =
        ∑ k,
          4 * D.delta k /
            ((1 - r)^2 * (D.gamma k)^2 + (1 + r + (1 - r) * D.delta k)^2) := by
  intro r _ _
  unfold XiEndpointAbsorptionData.profile
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact xiEndpointSingleNodeProfile_eq_kernel (D.gamma k) (D.delta k) r

end

end Omega.Zeta
