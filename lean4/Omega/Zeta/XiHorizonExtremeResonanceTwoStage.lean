import Omega.Zeta.XiHorizonEndpointAtomChristoffel
import Omega.Zeta.XiHorizonReflectionFiniteWitness

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-horizon-extreme-resonance-two-stage`. -/
theorem paper_xi_horizon_extreme_resonance_two_stage (alpha : Nat → Complex)
    (hSchur : XiSchurParameters alpha) (D : XiHorizonEndpointAtomChristoffelData) :
    ((∀ n : Nat, Complex.abs (alpha n) < 1) ∧ ((∃ N : Nat, 1 ≤ Complex.abs (alpha N)) → False)) ∧
      (D.atomMass = D.inverseSqNorm ∧ Tendsto D.christoffel atTop (𝓝 D.atomMass)) := by
  refine ⟨?_, ?_⟩
  · exact paper_xi_horizon_reflection_finite_witness alpha hSchur
  · exact paper_xi_horizon_endpoint_atom_christoffel D

end

end Omega.Zeta
