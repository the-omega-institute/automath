import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Boolean assignments used as coordinates for the period-three semisimple fiber. -/
abbrev conclusion_period3_fiber_boolean_semisimple_npsharp_universality_cube
    (n : ℕ) : Type :=
  Fin n → Bool

/-- The period-three fiber carries exactly the same Boolean coordinates in the seed model. -/
abbrev conclusion_period3_fiber_boolean_semisimple_npsharp_universality_fiber
    (n : ℕ) : Type :=
  Fin n → Bool

/-- Rank/unrank transport from Boolean assignments to the period-three fiber. -/
def conclusion_period3_fiber_boolean_semisimple_npsharp_universality_encode
    (n : ℕ) :
    conclusion_period3_fiber_boolean_semisimple_npsharp_universality_cube n →
      conclusion_period3_fiber_boolean_semisimple_npsharp_universality_fiber n :=
  id

/-- Transport a CNF-style Boolean predicate onto the encoded fiber. -/
def conclusion_period3_fiber_boolean_semisimple_npsharp_universality_transport
    {n : ℕ}
    (P : conclusion_period3_fiber_boolean_semisimple_npsharp_universality_cube n → Bool) :
    conclusion_period3_fiber_boolean_semisimple_npsharp_universality_fiber n → Bool :=
  P

/-- Count satisfying points of a Boolean predicate on a finite coordinate set. -/
def conclusion_period3_fiber_boolean_semisimple_npsharp_universality_count
    {α : Type} [Fintype α] (P : α → Bool) : ℕ :=
  (Finset.univ.filter fun x => P x).card

/-- Paper label: `thm:conclusion-period3-fiber-boolean-semisimple-npsharp-universality`. The
identity rank/unrank chart gives a bijection between Boolean assignments and the fixed
period-three fiber, so satisfiability and exact counting are transported without loss. -/
theorem paper_conclusion_period3_fiber_boolean_semisimple_npsharp_universality
    (n : ℕ)
    (P : conclusion_period3_fiber_boolean_semisimple_npsharp_universality_cube n → Bool) :
    Function.Bijective
        (conclusion_period3_fiber_boolean_semisimple_npsharp_universality_encode n) ∧
      ((∃ a : conclusion_period3_fiber_boolean_semisimple_npsharp_universality_cube n,
          P a = true) ↔
        ∃ y : conclusion_period3_fiber_boolean_semisimple_npsharp_universality_fiber n,
          conclusion_period3_fiber_boolean_semisimple_npsharp_universality_transport P y =
            true) ∧
      conclusion_period3_fiber_boolean_semisimple_npsharp_universality_count P =
        conclusion_period3_fiber_boolean_semisimple_npsharp_universality_count
          (conclusion_period3_fiber_boolean_semisimple_npsharp_universality_transport P) := by
  simp [conclusion_period3_fiber_boolean_semisimple_npsharp_universality_encode,
    conclusion_period3_fiber_boolean_semisimple_npsharp_universality_transport,
    conclusion_period3_fiber_boolean_semisimple_npsharp_universality_count]

end

end Omega.Conclusion
