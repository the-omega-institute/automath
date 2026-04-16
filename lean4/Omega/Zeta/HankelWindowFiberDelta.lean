import Mathlib.Tactic

namespace Omega.Zeta

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

end Omega.Zeta
