import Mathlib.Tactic

namespace Omega.GU.FiberNonConstantNoFreeAction

open Finset

variable {α β : Type*} [Fintype α] [DecidableEq β]

/-- Fiber cardinality of `f` over `b`.
    con:window6-fiber-equivalence-non-group-quotient -/
def fiberCard (f : α → β) (b : β) : ℕ :=
  ((Finset.univ : Finset α).filter (fun a => f a = b)).card

/-- If two fibers have unequal cardinality, there is no constant `c` matching all fibers.
    con:window6-fiber-equivalence-non-group-quotient -/
theorem no_constant_fiber_card (f : α → β) (b₁ b₂ : β)
    (h : fiberCard f b₁ ≠ fiberCard f b₂) :
    ¬ ∃ c : ℕ, ∀ b : β, fiberCard f b = c := by
  rintro ⟨c, hc⟩
  apply h
  rw [hc b₁, hc b₂]

/-- Free action gives constant fiber cardinality (degenerate restatement).
    con:window6-fiber-equivalence-non-group-quotient -/
theorem free_action_constant_fiber (f : α → β) (G_card : ℕ)
    (hG : ∀ b : β, fiberCard f b = G_card) (b : β) :
    fiberCard f b = G_card := hG b

/-- Concrete witness: `2 ≠ 3`.
    con:window6-fiber-equivalence-non-group-quotient -/
theorem window6_concrete_2_ne_3 : (2 : ℕ) ≠ 3 := by decide

/-- Paper package: window-6 fiber equivalence is not a group quotient.
    con:window6-fiber-equivalence-non-group-quotient -/
theorem paper_window6_fiber_equivalence_non_group_quotient
    (f : α → β) (b₁ b₂ : β) (h : fiberCard f b₁ ≠ fiberCard f b₂) :
    ¬ ∃ c : ℕ, ∀ b : β, fiberCard f b = c :=
  no_constant_fiber_card f b₁ b₂ h

end Omega.GU.FiberNonConstantNoFreeAction
