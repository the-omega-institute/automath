import Mathlib.Tactic
import Omega.Conclusion.ConnectedToDiscreteConstant

namespace Omega.CircleDimension

/-- Concrete data for a connected phase extension with a nontrivial profinite fiber. The fiber is
modeled as a finite discrete space, which is enough for the profinite obstruction used below. -/
structure ConnectedPhaseProfiniteFiberExtensionData where
  totalSpace : Type*
  quotient : Type*
  fiber : Type*
  totalTopology : TopologicalSpace totalSpace
  quotientTopology : TopologicalSpace quotient
  fiberTopology : TopologicalSpace fiber
  totalPreconnected : @PreconnectedSpace totalSpace totalTopology
  totalNonempty : Nonempty totalSpace
  quotientNonempty : Nonempty quotient
  fiberFintype : Fintype fiber
  fiberDiscrete : @DiscreteTopology fiber fiberTopology
  fiberNontrivial : ∃ a b : fiber, a ≠ b

namespace ConnectedPhaseProfiniteFiberExtensionData

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : TopologicalSpace D.totalSpace :=
  D.totalTopology

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : TopologicalSpace D.quotient :=
  D.quotientTopology

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : TopologicalSpace D.fiber :=
  D.fiberTopology

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : PreconnectedSpace D.totalSpace :=
  D.totalPreconnected

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : Nonempty D.totalSpace :=
  D.totalNonempty

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : Nonempty D.quotient :=
  D.quotientNonempty

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : Fintype D.fiber :=
  D.fiberFintype

instance (D : ConnectedPhaseProfiniteFiberExtensionData) : DiscreteTopology D.fiber :=
  D.fiberDiscrete

/-- Every continuous map from the connected total space to the profinite fiber is constant. -/
def noContinuousMapToFiber (D : ConnectedPhaseProfiniteFiberExtensionData) : Prop :=
  ∀ f : D.totalSpace → D.fiber, Continuous f → ∃ c : D.fiber, ∀ x : D.totalSpace, f x = c

/-- The extension does not split as a product of the torus quotient with the nontrivial profinite
fiber. -/
def notSplit (D : ConnectedPhaseProfiniteFiberExtensionData) : Prop :=
  ¬ Nonempty (D.totalSpace ≃ₜ D.quotient × D.fiber)

theorem noContinuousMapToFiber_holds (D : ConnectedPhaseProfiniteFiberExtensionData) :
    D.noContinuousMapToFiber := by
  intro f hf
  obtain ⟨x0⟩ := (inferInstance : Nonempty D.totalSpace)
  refine ⟨f x0, ?_⟩
  intro x
  exact Omega.Conclusion.ConnectedToDiscreteConstant.continuous_to_discrete_constant f hf x x0

theorem notSplit_holds (D : ConnectedPhaseProfiniteFiberExtensionData) :
    D.notSplit := by
  intro hSplit
  rcases hSplit with ⟨e⟩
  obtain ⟨a, b, hab⟩ := D.fiberNontrivial
  obtain ⟨q⟩ := (inferInstance : Nonempty D.quotient)
  let proj : D.totalSpace → D.fiber := fun x => (e x).2
  have hproj : Continuous proj := continuous_snd.comp e.continuous
  obtain ⟨c, hc⟩ := D.noContinuousMapToFiber_holds proj hproj
  have ha : a = c := by
    simpa [proj] using hc (e.symm (q, a))
  have hb : b = c := by
    simpa [proj] using hc (e.symm (q, b))
  exact hab (ha.trans hb.symm)

end ConnectedPhaseProfiniteFiberExtensionData

/-- Paper label: `thm:cdim-connected-phase-profinite-fiber-indecomposable`.
A connected phase space admits only constant maps to a profinite fiber, so a nontrivial profinite
factor cannot split off from the torus quotient. -/
theorem paper_cdim_connected_phase_profinite_fiber_indecomposable
    (D : ConnectedPhaseProfiniteFiberExtensionData) : D.noContinuousMapToFiber ∧ D.notSplit := by
  exact ⟨D.noContinuousMapToFiber_holds, D.notSplit_holds⟩

end Omega.CircleDimension
