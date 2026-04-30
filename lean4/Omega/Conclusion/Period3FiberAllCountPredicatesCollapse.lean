import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete fixed-fiber data for transporting count predicates to a period-three fiber. -/
structure conclusion_period3_fiber_all_count_predicates_collapse_data where
  conclusion_period3_fiber_all_count_predicates_collapse_width : ℕ := 0

namespace conclusion_period3_fiber_all_count_predicates_collapse_data

/-- Boolean assignments before the fixed-fiber transport. -/
abbrev conclusion_period3_fiber_all_count_predicates_collapse_source
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data) : Type :=
  Fin D.conclusion_period3_fiber_all_count_predicates_collapse_width → Bool

/-- The encoded period-three fiber; the fixed type records the same Boolean choices. -/
abbrev conclusion_period3_fiber_all_count_predicates_collapse_fiber
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data) : Type :=
  Fin D.conclusion_period3_fiber_all_count_predicates_collapse_width → Bool

/-- The parsimonious fixed-fiber reduction on assignments. -/
def conclusion_period3_fiber_all_count_predicates_collapse_reduction
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data) :
    D.conclusion_period3_fiber_all_count_predicates_collapse_source →
      D.conclusion_period3_fiber_all_count_predicates_collapse_fiber :=
  id

/-- Transport a predicate across the fixed-fiber reduction. -/
def conclusion_period3_fiber_all_count_predicates_collapse_transport
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data)
    (P : D.conclusion_period3_fiber_all_count_predicates_collapse_source → Bool) :
    D.conclusion_period3_fiber_all_count_predicates_collapse_fiber → Bool :=
  P

/-- Count the satisfying assignments of a predicate on a finite Boolean fiber. -/
def conclusion_period3_fiber_all_count_predicates_collapse_count
    {α : Type} [Fintype α] (P : α → Bool) : ℕ :=
  (Finset.univ.filter fun x => P x).card

/-- Generic PP-style majority count predicate. -/
def conclusion_period3_fiber_all_count_predicates_collapse_ppPredicate
    {α : Type} [Fintype α] (P : α → Bool) : Prop :=
  Fintype.card α / 2 < conclusion_period3_fiber_all_count_predicates_collapse_count P

/-- Generic parity count predicate. -/
def conclusion_period3_fiber_all_count_predicates_collapse_parityPredicate
    {α : Type} [Fintype α] (P : α → Bool) : Prop :=
  conclusion_period3_fiber_all_count_predicates_collapse_count P % 2 = 1

/-- Generic modular count predicate. -/
def conclusion_period3_fiber_all_count_predicates_collapse_modPredicate
    {α : Type} [Fintype α] (p r : ℕ) (P : α → Bool) : Prop :=
  conclusion_period3_fiber_all_count_predicates_collapse_count P % p = r

/-- Concrete statement for collapse of all count-only predicates to the fixed period-three fiber. -/
def conclusion_period3_fiber_all_count_predicates_collapse_statement
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data) : Prop :=
  ∀ P : D.conclusion_period3_fiber_all_count_predicates_collapse_source → Bool,
    conclusion_period3_fiber_all_count_predicates_collapse_count P =
        conclusion_period3_fiber_all_count_predicates_collapse_count
          (D.conclusion_period3_fiber_all_count_predicates_collapse_transport P) ∧
      (conclusion_period3_fiber_all_count_predicates_collapse_ppPredicate P ↔
        conclusion_period3_fiber_all_count_predicates_collapse_ppPredicate
          (D.conclusion_period3_fiber_all_count_predicates_collapse_transport P)) ∧
      (conclusion_period3_fiber_all_count_predicates_collapse_parityPredicate P ↔
        conclusion_period3_fiber_all_count_predicates_collapse_parityPredicate
          (D.conclusion_period3_fiber_all_count_predicates_collapse_transport P)) ∧
      ∀ p r : ℕ,
        conclusion_period3_fiber_all_count_predicates_collapse_modPredicate p r P ↔
          conclusion_period3_fiber_all_count_predicates_collapse_modPredicate p r
            (D.conclusion_period3_fiber_all_count_predicates_collapse_transport P)

end conclusion_period3_fiber_all_count_predicates_collapse_data

open conclusion_period3_fiber_all_count_predicates_collapse_data

/-- Paper label: `cor:conclusion-period3-fiber-all-count-predicates-collapse`. -/
theorem paper_conclusion_period3_fiber_all_count_predicates_collapse
    (D : conclusion_period3_fiber_all_count_predicates_collapse_data) :
    conclusion_period3_fiber_all_count_predicates_collapse_statement D := by
  intro P
  simp [conclusion_period3_fiber_all_count_predicates_collapse_transport,
    conclusion_period3_fiber_all_count_predicates_collapse_ppPredicate,
    conclusion_period3_fiber_all_count_predicates_collapse_parityPredicate,
    conclusion_period3_fiber_all_count_predicates_collapse_modPredicate,
    conclusion_period3_fiber_all_count_predicates_collapse_count]

end

end Omega.Conclusion
