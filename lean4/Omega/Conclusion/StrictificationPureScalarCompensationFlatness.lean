import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Fiber cardinality for a finite map, written with a paper-label prefix to avoid collisions. -/
def conclusion_strictification_pure_scalar_compensation_flatness_fiberCard
    {A B : Type*} [Fintype A] (h : A → B) (b : B) : ℕ := by
  classical
  exact ((Finset.univ : Finset A).filter fun a => h a = b).card

/-- The `g`-fiber over a downstream point. -/
def conclusion_strictification_pure_scalar_compensation_flatness_gFiber
    {Y Z : Type*} [Fintype Y] (g : Y → Z) (z : Z) : Finset Y := by
  classical
  exact (Finset.univ : Finset Y).filter fun y => g y = z

/-- Flatness means that the upstream fiber size is constant along every `g`-fiber. -/
def conclusion_strictification_pure_scalar_compensation_flatness_flat
    {X Y Z : Type*} [Fintype X] (f : X → Y) (g : Y → Z) : Prop :=
  ∀ z y₁ y₂, g y₁ = z → g y₂ = z →
    conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y₁ =
      conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y₂

/-- The expanded finite-fiber identity for the composite map. -/
def conclusion_strictification_pure_scalar_compensation_flatness_fiberExpansion
    {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → Z) : Prop :=
  ∀ z,
    conclusion_strictification_pure_scalar_compensation_flatness_fiberCard (g ∘ f) z =
      ∑ y ∈ conclusion_strictification_pure_scalar_compensation_flatness_gFiber g z,
        conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y

/-- The finite pure-scalar lift equality: the composite fiber count expands over `g`-fibers,
and scalar compensation is flat precisely when the upstream counts are fiberwise constant. -/
def conclusion_strictification_pure_scalar_compensation_flatness_liftEquality
    {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → Z) : Prop :=
  conclusion_strictification_pure_scalar_compensation_flatness_fiberExpansion f g ∧
    conclusion_strictification_pure_scalar_compensation_flatness_flat f g

/-- Paper-facing predicate for
`prop:conclusion-strictification-pure-scalar-compensation-flatness`. -/
def conclusion_strictification_pure_scalar_compensation_flatness_statement
    {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → Z) : Prop :=
  conclusion_strictification_pure_scalar_compensation_flatness_liftEquality f g ↔
    conclusion_strictification_pure_scalar_compensation_flatness_flat f g

lemma conclusion_strictification_pure_scalar_compensation_flatness_composite_card
    {X Y Z : Type*} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → Z) (z : Z) :
    conclusion_strictification_pure_scalar_compensation_flatness_fiberCard (g ∘ f) z =
      ∑ y ∈ conclusion_strictification_pure_scalar_compensation_flatness_gFiber g z,
        conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y := by
  classical
  let s : Finset X := (Finset.univ : Finset X).filter fun x => g (f x) = z
  let t : Finset Y := conclusion_strictification_pure_scalar_compensation_flatness_gFiber g z
  have hmaps : (s : Set X).MapsTo f t := by
    intro x hx
    simp [s, t, conclusion_strictification_pure_scalar_compensation_flatness_gFiber] at hx ⊢
    exact hx
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := t) hmaps
  have hinner :
      ∀ y ∈ t,
        ((s.filter fun x => f x = y).card =
          ((Finset.univ : Finset X).filter fun x => f x = y).card) := by
    intro y hy
    apply congrArg Finset.card
    ext x
    simp [s, t, conclusion_strictification_pure_scalar_compensation_flatness_gFiber] at hy ⊢
    intro hx
    simpa [hx] using hy
  calc
    conclusion_strictification_pure_scalar_compensation_flatness_fiberCard (g ∘ f) z
        = s.card := by
            simp [s, conclusion_strictification_pure_scalar_compensation_flatness_fiberCard]
    _ = ∑ y ∈ t, (s.filter fun x => f x = y).card := h
    _ = ∑ y ∈ t,
          conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hinner y hy]
            simp [conclusion_strictification_pure_scalar_compensation_flatness_fiberCard]
    _ = ∑ y ∈ conclusion_strictification_pure_scalar_compensation_flatness_gFiber g z,
          conclusion_strictification_pure_scalar_compensation_flatness_fiberCard f y := by
            rfl

/-- Paper label: `prop:conclusion-strictification-pure-scalar-compensation-flatness`. -/
theorem paper_conclusion_strictification_pure_scalar_compensation_flatness {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (f : X → Y) (g : Y → Z) :
    conclusion_strictification_pure_scalar_compensation_flatness_statement f g := by
  constructor
  · intro h
    exact h.2
  · intro hflat
    exact ⟨conclusion_strictification_pure_scalar_compensation_flatness_composite_card f g, hflat⟩

end

end Omega.Conclusion
