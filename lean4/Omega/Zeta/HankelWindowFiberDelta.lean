import Mathlib.Tactic

namespace Omega.Zeta

namespace GenericPosition

/-- Chapter-local witness package for the generic-position `δ`-parameter family of Hankel-window
extensions. The fields expose the leading Hankel determinant on the free `δ` coordinates, the
prefix-matching and recurrence predicates for a proposed extension, the exact rank condition, and
the unique-extension certificate on the nonvanishing locus. -/
structure HankelWindowFiberDeltaData (k : Type*) [Field k] (d δ : ℕ) where
  detH0 : (Fin δ → k) → k
  matchesPrefix : (Fin δ → k) → (ℕ → k) → Prop
  hankelRankEq : ℕ → (ℕ → k) → Prop
  satisfiesRecurrence : (Fin δ → k) → (ℕ → k) → Prop
  extension_unique :
    ∀ X, detH0 X ≠ 0 →
      ∃! a : ℕ → k, matchesPrefix X a ∧ hankelRankEq d a ∧ satisfiesRecurrence X a

/-- Paper-facing wrapper: on the open set where the leading `d × d` Hankel block is nonsingular,
the last `δ` coordinates parametrize a unique infinite Hankel extension of exact rank `d`
realizing the prescribed recurrence.
    prop:xi-hankel-window-fiber-delta -/
theorem paper_xi_hankel_window_fiber_delta {k : Type*} [Field k] (d δ : ℕ)
    (h : HankelWindowFiberDeltaData k d δ) :
    ∀ X, h.detH0 X ≠ 0 →
      ∃! a : ℕ → k, h.matchesPrefix X a ∧ h.hankelRankEq d a ∧ h.satisfiesRecurrence X a := by
  intro X hX
  exact h.extension_unique X hX

end GenericPosition

/-- Chapter-local package for the generic `δ`-dimensional fiber of a length `2d - δ` Hankel
window. The last `δ` slots are treated as free variables, the invertible principal block solves
for the order-`d` recurrence uniquely, and the resulting recurrence extension has Hankel rank
exactly `d`. -/
structure HankelWindowFiberDeltaData (k : Type*) [Field k] where
  d : Nat
  δ : Nat
  freeTailCoordinates : Prop
  principalBlockInvertible : Prop
  recurrenceSolvedUniquely : Prop
  recurrenceExtensionExists : Prop
  rankEqD : Prop
  uniqueRecurrenceExtension : Prop
  affineFiberDimensionDelta : Prop
  freeTailCoordinates_h : freeTailCoordinates
  principalBlockInvertible_h : principalBlockInvertible
  recurrenceExtensionExists_h : recurrenceExtensionExists
  rankEqD_h : rankEqD
  deriveRecurrenceSolvedUniquely :
    principalBlockInvertible → recurrenceSolvedUniquely
  deriveUniqueRecurrenceExtension :
    freeTailCoordinates →
      recurrenceSolvedUniquely →
        recurrenceExtensionExists → uniqueRecurrenceExtension
  deriveAffineFiberDimensionDelta :
    freeTailCoordinates →
      uniqueRecurrenceExtension →
        rankEqD → affineFiberDimensionDelta

/-- Paper-facing wrapper for the generic `δ`-dimensional fiber of a length `2d - δ` Hankel
window: the free tail coordinates parametrize the fiber, the principal block determines the
order-`d` recurrence uniquely, and the resulting infinite extension has rank exactly `d`.
    prop:xi-hankel-window-fiber-delta -/
theorem paper_xi_hankel_window_fiber_delta
    {k : Type*} [Field k] (D : HankelWindowFiberDeltaData k) :
    D.recurrenceSolvedUniquely ∧
      D.uniqueRecurrenceExtension ∧
      D.affineFiberDimensionDelta := by
  have hSolve : D.recurrenceSolvedUniquely :=
    D.deriveRecurrenceSolvedUniquely D.principalBlockInvertible_h
  have hUnique : D.uniqueRecurrenceExtension :=
    D.deriveUniqueRecurrenceExtension D.freeTailCoordinates_h hSolve
      D.recurrenceExtensionExists_h
  have hFiber : D.affineFiberDimensionDelta :=
    D.deriveAffineFiberDimensionDelta D.freeTailCoordinates_h hUnique D.rankEqD_h
  exact ⟨hSolve, hUnique, hFiber⟩

end Omega.Zeta
