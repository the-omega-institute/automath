import Mathlib.Tactic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.ContinuousMonoidHom

namespace Omega.Conclusion.ConnectedToDiscreteConstant

open Topology Set

variable {X F : Type*} [TopologicalSpace X] [TopologicalSpace F]

/-- A preconnected set in a discrete space is a subsingleton.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem subsingleton_of_preconnected_discrete [DiscreteTopology F]
    (S : Set F) (hS : IsPreconnected S) : S.Subsingleton :=
  hS.subsingleton

/-- A continuous map from a preconnected space to a discrete space has
    subsingleton range.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem continuous_to_discrete_image_subsingleton
    [PreconnectedSpace X] [DiscreteTopology F]
    (f : X → F) (hf : Continuous f) : (Set.range f).Subsingleton := by
  have hrange : IsPreconnected (Set.range f) :=
    isPreconnected_range hf
  exact subsingleton_of_preconnected_discrete _ hrange

/-- A continuous map from a preconnected space to a discrete space is constant.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem continuous_to_discrete_constant
    [PreconnectedSpace X] [DiscreteTopology F]
    (f : X → F) (hf : Continuous f) (x y : X) : f x = f y := by
  have hsub := continuous_to_discrete_image_subsingleton f hf
  exact hsub ⟨x, rfl⟩ ⟨y, rfl⟩

/-- A continuous map from a nonempty preconnected space to a discrete space
    is equal to some constant value.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem continuous_to_discrete_eq_const
    [PreconnectedSpace X] [DiscreteTopology F] [Nonempty X]
    (f : X → F) (hf : Continuous f) : ∃ c : F, ∀ x : X, f x = c := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  exact ⟨f x₀, fun x => continuous_to_discrete_constant f hf x x₀⟩

/-- A continuous additive homomorphism from a preconnected additive group to a
    discrete additive group is zero.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem continuous_hom_connected_to_discrete_zero
    {X F : Type*} [AddGroup X] [TopologicalSpace X] [PreconnectedSpace X]
    [AddGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (f : X →+ F) (hf : Continuous f) : ∀ x : X, f x = 0 := by
  intro x
  have h0 : f x = f 0 := continuous_to_discrete_constant (f : X → F) hf x 0
  rw [h0, f.map_zero]

/-- Paper package: screen-phase universal solenoid no finite torsion.
    thm:conclusion-screenphase-universal-solenoid-no-finite-torsion -/
theorem paper_screenphase_universal_solenoid_no_finite_torsion
    {X F : Type*} [AddGroup X] [TopologicalSpace X] [PreconnectedSpace X]
    [AddGroup F] [TopologicalSpace F] [DiscreteTopology F]
    (f : X →+ F) (hf : Continuous f) : ∀ x : X, f x = 0 :=
  continuous_hom_connected_to_discrete_zero f hf

end Omega.Conclusion.ConnectedToDiscreteConstant
