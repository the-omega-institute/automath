import Mathlib.Tactic

namespace Omega.Conclusion

universe u v w x

/-- Concrete quotient package for the observer-visible Čech cocycle.
The data records the coefficient object, its strict visible quotient, the chosen cocycle
representatives, their pointwise vanishing after projection, and the universal property of the
quotient projection for maps constant on projection fibers. -/
structure conclusion_observer_initial_visible_quotient_gerbe_neutralization_data where
  Coeff : Type u
  VisibleCoeff : Type v
  CocycleIndex : Type w
  visibleZero : VisibleCoeff
  proj : Coeff → VisibleCoeff
  cocycle : CocycleIndex → Coeff
  conclusion_observer_initial_visible_quotient_gerbe_neutralization_cocycle_projection_zero :
    ∀ i : CocycleIndex, proj (cocycle i) = visibleZero
  conclusion_observer_initial_visible_quotient_gerbe_neutralization_quotient_universal :
    ∀ {B : Type x} (φ : Coeff → B),
      (∀ a b : Coeff, proj a = proj b → φ a = φ b) →
        ∃! ψ : VisibleCoeff → B, ∀ a : Coeff, φ a = ψ (proj a)

namespace conclusion_observer_initial_visible_quotient_gerbe_neutralization_data

/-- The chosen Čech cocycle vanishes after projection to the strict visible quotient. -/
def cocycleVanishesInVisibleQuotient
    (D : conclusion_observer_initial_visible_quotient_gerbe_neutralization_data) : Prop :=
  ∀ i : D.CocycleIndex, D.proj (D.cocycle i) = D.visibleZero

/-- Neutrality of the associated quotient gerbe is represented by the zero visible cocycle. -/
def gerbeNeutral
    (D : conclusion_observer_initial_visible_quotient_gerbe_neutralization_data) : Prop :=
  D.cocycleVanishesInVisibleQuotient

/-- A map kills the quotient cocycle exactly when it is constant on projection fibers. -/
def killsCocycle
    (D : conclusion_observer_initial_visible_quotient_gerbe_neutralization_data)
    {B : Type*} (φ : D.Coeff → B) : Prop :=
  ∀ a b : D.Coeff, D.proj a = D.proj b → φ a = φ b

end conclusion_observer_initial_visible_quotient_gerbe_neutralization_data

/-- Paper label: `thm:conclusion-observer-initial-visible-quotient-gerbe-neutralization`. -/
theorem paper_conclusion_observer_initial_visible_quotient_gerbe_neutralization
    (D : conclusion_observer_initial_visible_quotient_gerbe_neutralization_data.{u, v, w, x}) :
    D.cocycleVanishesInVisibleQuotient ∧ D.gerbeNeutral ∧
      ∀ {B : Type x} (φ : D.Coeff → B), D.killsCocycle φ →
        ∃! ψ : D.VisibleCoeff → B, ∀ a, φ a = ψ (D.proj a) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      D.conclusion_observer_initial_visible_quotient_gerbe_neutralization_cocycle_projection_zero
  · exact
      D.conclusion_observer_initial_visible_quotient_gerbe_neutralization_cocycle_projection_zero
  · intro B φ hφ
    exact
      D.conclusion_observer_initial_visible_quotient_gerbe_neutralization_quotient_universal φ
        (by
          simpa [
            conclusion_observer_initial_visible_quotient_gerbe_neutralization_data.killsCocycle]
            using hφ)

end Omega.Conclusion
