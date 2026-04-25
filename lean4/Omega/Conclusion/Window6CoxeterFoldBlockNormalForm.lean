import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The cyclic sector is the same `18`-word audited necklace model used in the block normal form. -/
abbrev conclusion_window6_coxeter_fold_block_normal_form_cyclic_word : Type :=
  Fin 3 × Fin 6

/-- The short-root cyclic block label. -/
def conclusion_window6_coxeter_fold_block_normal_form_short_orbit : Fin 3 := 0

/-- The first long-root cyclic block label. -/
def conclusion_window6_coxeter_fold_block_normal_form_long_orbit_a : Fin 3 := 1

/-- The second long-root cyclic block label. -/
def conclusion_window6_coxeter_fold_block_normal_form_long_orbit_b : Fin 3 := 2

/-- The cyclic Coxeter step inside each length-`6` block. -/
def conclusion_window6_coxeter_fold_block_normal_form_cyclic_operator :
    conclusion_window6_coxeter_fold_block_normal_form_cyclic_word →
      conclusion_window6_coxeter_fold_block_normal_form_cyclic_word
  | (orbit, position) => (orbit, position + 1)

/-- The ordered basis for the fold-block normal form consists of the `18` cyclic vectors together
with the `3` boundary vectors. -/
abbrev conclusion_window6_coxeter_fold_block_normal_form_basis : Type :=
  conclusion_window6_coxeter_fold_block_normal_form_cyclic_word ⊕ Fin 3

/-- The short-root cyclic block in the audited basis ordering. -/
def conclusion_window6_coxeter_fold_block_normal_form_short_block :
    List conclusion_window6_coxeter_fold_block_normal_form_basis :=
  List.ofFn fun position : Fin 6 =>
    Sum.inl (conclusion_window6_coxeter_fold_block_normal_form_short_orbit, position)

/-- The first long-root cyclic block in the audited basis ordering. -/
def conclusion_window6_coxeter_fold_block_normal_form_long_block_a :
    List conclusion_window6_coxeter_fold_block_normal_form_basis :=
  List.ofFn fun position : Fin 6 =>
    Sum.inl (conclusion_window6_coxeter_fold_block_normal_form_long_orbit_a, position)

/-- The second long-root cyclic block in the audited basis ordering. -/
def conclusion_window6_coxeter_fold_block_normal_form_long_block_b :
    List conclusion_window6_coxeter_fold_block_normal_form_basis :=
  List.ofFn fun position : Fin 6 =>
    Sum.inl (conclusion_window6_coxeter_fold_block_normal_form_long_orbit_b, position)

/-- The boundary identity block. -/
def conclusion_window6_coxeter_fold_block_normal_form_boundary_block :
    List conclusion_window6_coxeter_fold_block_normal_form_basis :=
  List.ofFn fun boundary : Fin 3 => Sum.inr boundary

/-- The basis order induced by the three-necklace decomposition. -/
def conclusion_window6_coxeter_fold_block_normal_form_ordered_basis :
    List conclusion_window6_coxeter_fold_block_normal_form_basis :=
  conclusion_window6_coxeter_fold_block_normal_form_short_block ++
    conclusion_window6_coxeter_fold_block_normal_form_long_block_a ++
      conclusion_window6_coxeter_fold_block_normal_form_long_block_b ++
        conclusion_window6_coxeter_fold_block_normal_form_boundary_block

/-- The audited multiplicity diagonal records the three cyclic `6`-blocks and the boundary
identity `3`-block. -/
def conclusion_window6_coxeter_fold_block_normal_form_multiplicity_diagonal : List ℕ :=
  [6, 6, 6, 3]

/-- The block-diagonal Coxeter operator on the ordered basis: three cyclic `6`-blocks together
with the boundary identity block. -/
def conclusion_window6_coxeter_fold_block_normal_form_operator :
    conclusion_window6_coxeter_fold_block_normal_form_basis →
      conclusion_window6_coxeter_fold_block_normal_form_basis
  | Sum.inl word =>
      Sum.inl (conclusion_window6_coxeter_fold_block_normal_form_cyclic_operator word)
  | Sum.inr boundary => Sum.inr boundary

/-- Paper-facing normal-form statement for the window-`6` fold block decomposition. -/
def conclusion_window6_coxeter_fold_block_normal_form_statement : Prop :=
  Fintype.card conclusion_window6_coxeter_fold_block_normal_form_basis = 21 ∧
    conclusion_window6_coxeter_fold_block_normal_form_short_block.length = 6 ∧
    conclusion_window6_coxeter_fold_block_normal_form_long_block_a.length = 6 ∧
    conclusion_window6_coxeter_fold_block_normal_form_long_block_b.length = 6 ∧
    conclusion_window6_coxeter_fold_block_normal_form_boundary_block.length = 3 ∧
    conclusion_window6_coxeter_fold_block_normal_form_ordered_basis.length = 21 ∧
    conclusion_window6_coxeter_fold_block_normal_form_multiplicity_diagonal = [6, 6, 6, 3] ∧
    (∀ word,
      conclusion_window6_coxeter_fold_block_normal_form_operator (Sum.inl word) =
        Sum.inl (conclusion_window6_coxeter_fold_block_normal_form_cyclic_operator word)) ∧
    (∀ boundary,
      conclusion_window6_coxeter_fold_block_normal_form_operator (Sum.inr boundary) =
        Sum.inr boundary) ∧
    (∀ v, (conclusion_window6_coxeter_fold_block_normal_form_operator^[6]) v = v)

private theorem conclusion_window6_coxeter_fold_block_normal_form_cyclic_operator_order_six
    (w : conclusion_window6_coxeter_fold_block_normal_form_cyclic_word) :
    (conclusion_window6_coxeter_fold_block_normal_form_cyclic_operator^[6]) w = w := by
  rcases w with ⟨orbit, position⟩
  fin_cases orbit <;> fin_cases position <;> rfl

private theorem conclusion_window6_coxeter_fold_block_normal_form_operator_order_six
    (v : conclusion_window6_coxeter_fold_block_normal_form_basis) :
    (conclusion_window6_coxeter_fold_block_normal_form_operator^[6]) v = v := by
  rcases v with w | boundary
  · rcases w with ⟨orbit, position⟩
    fin_cases orbit <;> fin_cases position <;> rfl
  · fin_cases boundary <;> rfl

/-- Paper label: `thm:conclusion-window6-coxeter-fold-block-normal-form`. -/
theorem paper_conclusion_window6_coxeter_fold_block_normal_form :
    conclusion_window6_coxeter_fold_block_normal_form_statement := by
  refine ⟨by simp [conclusion_window6_coxeter_fold_block_normal_form_basis], by simp
    [conclusion_window6_coxeter_fold_block_normal_form_short_block], by simp
    [conclusion_window6_coxeter_fold_block_normal_form_long_block_a], by simp
    [conclusion_window6_coxeter_fold_block_normal_form_long_block_b], by simp
    [conclusion_window6_coxeter_fold_block_normal_form_boundary_block], by simp
    [conclusion_window6_coxeter_fold_block_normal_form_ordered_basis,
      conclusion_window6_coxeter_fold_block_normal_form_short_block,
      conclusion_window6_coxeter_fold_block_normal_form_long_block_a,
      conclusion_window6_coxeter_fold_block_normal_form_long_block_b,
      conclusion_window6_coxeter_fold_block_normal_form_boundary_block], rfl, ?_, ?_, ?_⟩
  · intro word
    rfl
  · intro boundary
    rfl
  · intro v
    exact conclusion_window6_coxeter_fold_block_normal_form_operator_order_six v

end Omega.Conclusion
