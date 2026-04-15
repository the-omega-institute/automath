import Mathlib.Tactic

namespace Omega.Folding.CandidateSetMonotone

open Finset

variable {α β : Type*} [DecidableEq β]

/-- Successor set: union of `f v` across `v ∈ S`.
    prop:det-candidate-set-monotone -/
noncomputable def succSet (f : α → Option β) (S : Finset α) : Finset β :=
  S.biUnion (fun v => (f v).toFinset)

omit [DecidableEq β] in
/-- An `Option.toFinset` has cardinality at most 1.
    prop:det-candidate-set-monotone -/
theorem option_toFinset_card_le_one (o : Option β) : o.toFinset.card ≤ 1 := by
  cases o with
  | none => simp
  | some b => simp

/-- Candidate set monotonicity: `|succSet f S| ≤ |S|`.
    prop:det-candidate-set-monotone -/
theorem paper_det_candidate_set_monotone
    [DecidableEq α] (f : α → Option β) (S : Finset α) :
    (succSet f S).card ≤ S.card := by
  unfold succSet
  calc (S.biUnion (fun v => (f v).toFinset)).card
      ≤ ∑ v ∈ S, ((f v).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, 1 :=
        Finset.sum_le_sum (fun v _ => option_toFinset_card_le_one (f v))
    _ = S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- Singleton case: `|succSet f {v}| ≤ 1`.
    prop:det-candidate-set-monotone -/
theorem succSet_singleton [DecidableEq α] (f : α → Option β) (v : α) :
    (succSet f {v}).card ≤ 1 := by
  have := paper_det_candidate_set_monotone f ({v} : Finset α)
  simp at this
  exact this

/-- If `f v = some b`, then `succSet f {v} = {b}`.
    prop:det-candidate-set-monotone -/
theorem succSet_singleton_of_some [DecidableEq α]
    (f : α → Option β) (v : α) (b : β) (h : f v = some b) :
    succSet f {v} = {b} := by
  unfold succSet
  rw [Finset.singleton_biUnion, h]
  rfl

/-- If `f v = none`, then `succSet f {v} = ∅`.
    prop:det-candidate-set-monotone -/
theorem succSet_singleton_of_none [DecidableEq α]
    (f : α → Option β) (v : α) (h : f v = none) :
    succSet f {v} = ∅ := by
  unfold succSet
  rw [Finset.singleton_biUnion, h]
  rfl

end Omega.Folding.CandidateSetMonotone
