import Mathlib.Tactic
import Omega.Zeta.XiPickPoissonDetScalingLaw

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete data for the anchored capacity stabilizer covariance statement. The scaled Pick--
Poisson package keeps the pseudohyperbolic factors fixed, scales every endpoint Poisson weight by
`m^-1`, and records the matching capacity scaling. -/
structure xi_anchored_capacity_stabilizer_covariance_data where
  kappa : ℕ
  m : ℝ
  hm : 0 < m
  p : Fin kappa → ℝ
  pScaled : Fin kappa → ℝ
  rho : Fin kappa → Fin kappa → ℝ
  rhoScaled : Fin kappa → Fin kappa → ℝ
  detP : ℝ
  detPScaled : ℝ
  capacity : ℝ
  capacityScaled : ℝ
  hrhoScaled : ∀ j k, rhoScaled j k = rho j k
  hpScaled : ∀ j, pScaled j = p j / m
  hdet :
    detP =
      (∏ j, p j) * ∏ j : Fin kappa, ∏ k : Fin kappa, if j < k then rho j k ^ 2 else 1
  hdetScaled :
    detPScaled =
      (∏ j, pScaled j) *
        ∏ j : Fin kappa, ∏ k : Fin kappa, if j < k then rhoScaled j k ^ 2 else 1
  hcapacityScaled : capacityScaled = capacity / m

namespace xi_anchored_capacity_stabilizer_covariance_data

/-- The pseudohyperbolic distances are invariant under the anchored stabilizer action. -/
def pseudohyperbolicInvariant (D : xi_anchored_capacity_stabilizer_covariance_data) : Prop :=
  ∀ j k, D.rhoScaled j k = D.rho j k

/-- Endpoint Poisson weights scale by the anchored dilation factor. -/
def poissonWeightCovariant (D : xi_anchored_capacity_stabilizer_covariance_data) : Prop :=
  ∀ j, D.pScaled j = D.p j / D.m

/-- The Pick--Poisson determinant picks up one factor of `m^-1` for every endpoint. -/
def detCovariant (D : xi_anchored_capacity_stabilizer_covariance_data) : Prop :=
  D.detPScaled = D.detP / D.m ^ D.kappa

/-- The anchored capacity has the same endpoint homogeneity as the Poisson weights. -/
def capacityCovariant (D : xi_anchored_capacity_stabilizer_covariance_data) : Prop :=
  D.capacityScaled = D.capacity / D.m

end xi_anchored_capacity_stabilizer_covariance_data

/-- Paper label: `cor:xi-anchored-capacity-stabilizer-covariance`. -/
theorem paper_xi_anchored_capacity_stabilizer_covariance
    (D : xi_anchored_capacity_stabilizer_covariance_data) :
    D.pseudohyperbolicInvariant ∧ D.poissonWeightCovariant ∧ D.detCovariant ∧
      D.capacityCovariant := by
  have hdetScaled_rho :
      D.detPScaled =
        (∏ j, D.pScaled j) *
          ∏ j : Fin D.kappa, ∏ k : Fin D.kappa, if j < k then D.rho j k ^ 2 else 1 := by
    rw [D.hdetScaled]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro j _hj
    refine Finset.prod_congr rfl ?_
    intro k _hk
    by_cases hlt : j < k
    · simp [hlt, D.hrhoScaled j k]
    · simp [hlt]
  have hdet :
      D.detPScaled = D.detP / D.m ^ D.kappa :=
    paper_xi_pick_poisson_det_scaling_law D.m D.hm D.p D.pScaled D.rho D.detP
      D.detPScaled D.hpScaled D.hdet hdetScaled_rho
  exact ⟨D.hrhoScaled, D.hpScaled, hdet, D.hcapacityScaled⟩

end Omega.Zeta
