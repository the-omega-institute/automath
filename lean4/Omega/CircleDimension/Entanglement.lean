import Mathlib.Data.Complex.Basic
import Omega.CircleDimension.HilbertCarrier

namespace Omega.CircleDimension

universe u v

/-- A concrete pure-ray representative in the composite carrier of two subsystems. The minimal
formalization records the composite amplitude profile together with a nonzero coefficient, which is
enough to model a genuine ray. -/
structure EntanglementData where
  Left : Type u
  Right : Type v
  ray : Left → Right → ℂ
  ray_nonzero : ∃ x : Left, ∃ y : Right, ray x y ≠ 0

/-- A composite ray is simple when it factorizes into local amplitudes. -/
def EntanglementData.simple_tensor_ray (D : EntanglementData) : Prop :=
  ∃ ψ₁ : D.Left → ℂ, ∃ ψ₂ : D.Right → ℂ, ∀ x y, D.ray x y = ψ₁ x * ψ₂ y

/-- The paper's "not a simple tensor" condition. -/
def EntanglementData.not_simple_tensor_ray (D : EntanglementData) : Prop :=
  ¬ D.simple_tensor_ray

/-- In this concrete wrapper, a pure ray is represented by a nonzero amplitude profile. -/
def EntanglementData.pure_ray (D : EntanglementData) : Prop :=
  ∃ x : D.Left, ∃ y : D.Right, D.ray x y ≠ 0

/-- An entangled ray is a pure ray that is not a simple tensor. -/
def EntanglementData.entangled_ray (D : EntanglementData) : Prop :=
  D.pure_ray ∧ D.not_simple_tensor_ray

/-- Paper label: `cor:cdim-entanglement`. -/
theorem paper_cdim_entanglement (D : EntanglementData) :
    D.not_simple_tensor_ray → D.entangled_ray := by
  intro hnot
  exact ⟨D.ray_nonzero, hnot⟩

end Omega.CircleDimension
