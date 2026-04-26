import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.Connected.Basic
import Omega.Conclusion.ConnectedToDiscreteConstant

namespace Omega.Conclusion

/-- Concrete finite-window Lie-action data: `K0` models the connected component, `K` the ambient
group, `Q` the component group, and the finite action is recorded as a hom into a permutation
group. Equality in the component group is witnessed by multiplication with an element of the
connected component. -/
structure ConclusionFiniteWindowConnectedLieFactorCollapseData where
  K : Type
  K0 : Type
  X : Type
  Q : Type
  groupK : Group K
  groupK0 : Group K0
  fintypeX : Fintype X
  decidableEqX : DecidableEq X
  groupQ : Group Q
  topologicalSpaceK0 : TopologicalSpace K0
  preconnectedSpaceK0 : @PreconnectedSpace K0 topologicalSpaceK0
  componentInclusion : K0 →* K
  quotientMap : K →* Q
  action : K →* Equiv.Perm X
  connectedActionContinuous :
    @Continuous K0 (Equiv.Perm X) topologicalSpaceK0 ⊥
      (fun k0 => action (componentInclusion k0))
  sameComponentWitness :
    ∀ g h : K, quotientMap g = quotientMap h →
      ∃ k0 : K0, action g = action h * action (componentInclusion k0)

attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.groupK
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.groupK0
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.fintypeX
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.decidableEqX
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.groupQ
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.topologicalSpaceK0
attribute [instance] ConclusionFiniteWindowConnectedLieFactorCollapseData.preconnectedSpaceK0

namespace ConclusionFiniteWindowConnectedLieFactorCollapseData

/-- The connected component acts trivially on the finite discrete set. -/
def connected_component_acts_trivially
    (D : ConclusionFiniteWindowConnectedLieFactorCollapseData) : Prop :=
  ∀ k0 : D.K0, ∀ x : D.X, D.action (D.componentInclusion k0) x = x

/-- The permutation action factors through the component group, hence the orbit decomposition also
does. We record the stronger statement that equal component-group classes induce the same
permutation. -/
def orbit_decomposition_factors_through_component_group
    (D : ConclusionFiniteWindowConnectedLieFactorCollapseData) : Prop :=
  ∀ g h : D.K, D.quotientMap g = D.quotientMap h → D.action g = D.action h

end ConclusionFiniteWindowConnectedLieFactorCollapseData

open ConclusionFiniteWindowConnectedLieFactorCollapseData

/-- Paper label: `thm:conclusion-finite-window-connected-lie-factor-collapse`. A continuous action
of a connected component on a finite discrete set has trivial image in the finite permutation
group, so the full finite-window orbit decomposition factors through the component group. -/
theorem paper_conclusion_finite_window_connected_lie_factor_collapse
    (D : ConclusionFiniteWindowConnectedLieFactorCollapseData) :
    D.connected_component_acts_trivially ∧ D.orbit_decomposition_factors_through_component_group := by
  have htriv_perm : ∀ k0 : D.K0, D.action (D.componentInclusion k0) = 1 := by
    intro k0
    ext x
    letI : TopologicalSpace (Equiv.Perm D.X) := ⊥
    letI : DiscreteTopology (Equiv.Perm D.X) := ⟨rfl⟩
    have hconst :
        D.action (D.componentInclusion k0) = D.action (D.componentInclusion (1 : D.K0)) := by
      simpa using
        Omega.Conclusion.ConnectedToDiscreteConstant.continuous_to_discrete_constant
          (f := fun g0 => D.action (D.componentInclusion g0)) D.connectedActionContinuous
          k0 (1 : D.K0)
    simpa using congrArg (fun σ : Equiv.Perm D.X => σ x) hconst
  refine ⟨?_, ?_⟩
  · intro k0 x
    simpa using congrArg (fun σ : Equiv.Perm D.X => σ x) (htriv_perm k0)
  · intro g h hq
    rcases D.sameComponentWitness g h hq with ⟨k0, hk0⟩
    rw [hk0, htriv_perm k0, mul_one]

end Omega.Conclusion
