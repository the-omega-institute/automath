import Mathlib.Tactic
import Mathlib.Topology.Connected.TotallyDisconnected

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part69c-localized-dual-finite-visible-collapse`. -/
theorem paper_xi_time_part69c_localized_dual_finite_visible_collapse
    {Sigma A : Type*} [TopologicalSpace Sigma] [TopologicalSpace A] [ConnectedSpace Sigma]
    [Finite A] [DiscreteTopology A] (F : Sigma → A) (hF : Continuous F) :
    ∃ a : A, ∀ x : Sigma, F x = a := by
  refine ⟨F (Classical.arbitrary Sigma), ?_⟩
  intro x
  exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace Sigma) hF

end Omega.Zeta
