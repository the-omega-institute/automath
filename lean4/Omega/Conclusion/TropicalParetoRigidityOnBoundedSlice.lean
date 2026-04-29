import Mathlib.Tactic

namespace Omega.Conclusion

/-- A finite bounded slice equipped with a two-coordinate natural-number cost. -/
structure conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor where
  Slice : Type
  decEq : DecidableEq Slice
  finite : Fintype Slice
  base : Slice
  cost : Slice → ℕ × ℕ

/-- The finite cost image of a bounded slice. -/
noncomputable def conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    Finset (ℕ × ℕ) := by
  classical
  letI : DecidableEq C.Slice := C.decEq
  letI : Fintype C.Slice := C.finite
  exact Finset.univ.image C.cost

lemma conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image_nonempty
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    (conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C).Nonempty := by
  classical
  refine ⟨C.cost C.base, ?_⟩
  unfold conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image
  simp

/-- Two-coordinate tropical preorder: no larger in either cost coordinate. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_le
    (a b : ℕ × ℕ) : Prop :=
  a.1 ≤ b.1 ∧ a.2 ≤ b.2

/-- Strict descent in both cost coordinates. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_strict_two_coordinate_descent
    (a b : ℕ × ℕ) : Prop :=
  a.1 < b.1 ∧ a.2 < b.2

/-- Pareto minimality inside the finite cost image. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_is_pareto_minimal
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor)
    (z : ℕ × ℕ) : Prop :=
  z ∈ conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C ∧
    ∀ y, y ∈ conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C →
      conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_le y z →
        conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_le z y

/-- The finite Pareto front obtained by filtering the finite cost image. -/
noncomputable def conclusion_tropical_pareto_rigidity_on_bounded_slice_pareto_front
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    Finset (ℕ × ℕ) := by
  classical
  exact (conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C).filter
    (conclusion_tropical_pareto_rigidity_on_bounded_slice_is_pareto_minimal C)

/-- First coordinate of the coordinatewise infimum of the finite cost image. -/
noncomputable def conclusion_tropical_pareto_rigidity_on_bounded_slice_first_inf
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) : ℕ :=
  ((conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C).image
    (fun z : ℕ × ℕ => z.1)).min'
      (by
        rcases conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image_nonempty C
          with ⟨z, hz⟩
        exact ⟨z.1, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩)

/-- Second coordinate of the coordinatewise infimum of the finite cost image. -/
noncomputable def conclusion_tropical_pareto_rigidity_on_bounded_slice_second_inf
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) : ℕ :=
  ((conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C).image
    (fun z : ℕ × ℕ => z.2)).min'
      (by
        rcases conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image_nonempty C
          with ⟨z, hz⟩
        exact ⟨z.2, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩)

/-- The coordinatewise infimum point determined by the two finite coordinate images. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_is_coordinatewise_inf
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor)
    (z : ℕ × ℕ) : Prop :=
  z.1 = conclusion_tropical_pareto_rigidity_on_bounded_slice_first_inf C ∧
    z.2 = conclusion_tropical_pareto_rigidity_on_bounded_slice_second_inf C

/-- Finite tropical Pareto-front existence. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_tropical_multiplicative
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) : Prop :=
  ∃ F : Finset (ℕ × ℕ), ∀ z,
    z ∈ F ↔
      z ∈ conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C ∧
        conclusion_tropical_pareto_rigidity_on_bounded_slice_is_pareto_minimal C z

/-- Uniqueness of the coordinatewise infimum pair. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_unique_pareto_inf
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) : Prop :=
  ∃! z : ℕ × ℕ,
    conclusion_tropical_pareto_rigidity_on_bounded_slice_is_coordinatewise_inf C z

/-- Pareto minimal points have no simultaneous strict descent inside the finite image. -/
def conclusion_tropical_pareto_rigidity_on_bounded_slice_no_strict_two_coordinate_descent
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) : Prop :=
  ∀ z, z ∈ conclusion_tropical_pareto_rigidity_on_bounded_slice_pareto_front C →
    ∀ y, y ∈ conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_image C →
      ¬ conclusion_tropical_pareto_rigidity_on_bounded_slice_strict_two_coordinate_descent y z

lemma conclusion_tropical_pareto_rigidity_on_bounded_slice_tropical_multiplicative_verified
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    conclusion_tropical_pareto_rigidity_on_bounded_slice_tropical_multiplicative C := by
  classical
  refine ⟨conclusion_tropical_pareto_rigidity_on_bounded_slice_pareto_front C, ?_⟩
  intro z
  simp [conclusion_tropical_pareto_rigidity_on_bounded_slice_pareto_front]

lemma conclusion_tropical_pareto_rigidity_on_bounded_slice_unique_pareto_inf_verified
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    conclusion_tropical_pareto_rigidity_on_bounded_slice_unique_pareto_inf C := by
  refine
    ⟨(conclusion_tropical_pareto_rigidity_on_bounded_slice_first_inf C,
        conclusion_tropical_pareto_rigidity_on_bounded_slice_second_inf C), ?_, ?_⟩
  · exact ⟨rfl, rfl⟩
  · intro y hy
    rcases y with ⟨a, b⟩
    rcases hy with ⟨ha, hb⟩
    exact Prod.ext ha hb

lemma conclusion_tropical_pareto_rigidity_on_bounded_slice_no_strict_descent_verified
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    conclusion_tropical_pareto_rigidity_on_bounded_slice_no_strict_two_coordinate_descent C := by
  classical
  intro z hz y hy hstrict
  have hminimal :
      conclusion_tropical_pareto_rigidity_on_bounded_slice_is_pareto_minimal C z :=
    (Finset.mem_filter.mp hz).2
  have hback :
      conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_le z y :=
    hminimal.2 y hy ⟨Nat.le_of_lt hstrict.1, Nat.le_of_lt hstrict.2⟩
  exact (Nat.lt_irrefl y.1) (lt_of_lt_of_le hstrict.1 hback.1)

/-- Paper label: `thm:conclusion-tropical-pareto-rigidity-on-bounded-slice`. -/
theorem paper_conclusion_tropical_pareto_rigidity_on_bounded_slice
    (C : conclusion_tropical_pareto_rigidity_on_bounded_slice_cost_functor) :
    conclusion_tropical_pareto_rigidity_on_bounded_slice_tropical_multiplicative C ∧
      conclusion_tropical_pareto_rigidity_on_bounded_slice_unique_pareto_inf C ∧
      conclusion_tropical_pareto_rigidity_on_bounded_slice_no_strict_two_coordinate_descent C := by
  exact
    ⟨conclusion_tropical_pareto_rigidity_on_bounded_slice_tropical_multiplicative_verified C,
      conclusion_tropical_pareto_rigidity_on_bounded_slice_unique_pareto_inf_verified C,
      conclusion_tropical_pareto_rigidity_on_bounded_slice_no_strict_descent_verified C⟩

end Omega.Conclusion
