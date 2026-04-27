import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

universe u v

/-- Concrete surjection-and-section data for the commutative-monoid externalization package. -/
structure conclusion_cmon_externalization_initial_prime_register_data where
  conclusion_cmon_externalization_initial_prime_register_source : Type u
  conclusion_cmon_externalization_initial_prime_register_target : Type v
  conclusion_cmon_externalization_initial_prime_register_projection :
    conclusion_cmon_externalization_initial_prime_register_source →
      conclusion_cmon_externalization_initial_prime_register_target
  conclusion_cmon_externalization_initial_prime_register_section :
    conclusion_cmon_externalization_initial_prime_register_target →
      conclusion_cmon_externalization_initial_prime_register_source
  conclusion_cmon_externalization_initial_prime_register_section_right_inverse :
    Function.RightInverse conclusion_cmon_externalization_initial_prime_register_section
      conclusion_cmon_externalization_initial_prime_register_projection

namespace conclusion_cmon_externalization_initial_prime_register_data

/-- Points outside the chosen section are the prime-register generators. -/
abbrev conclusion_cmon_externalization_initial_prime_register_nonsection
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Type u :=
  {x : D.conclusion_cmon_externalization_initial_prime_register_source //
    D.conclusion_cmon_externalization_initial_prime_register_section
        (D.conclusion_cmon_externalization_initial_prime_register_projection x) ≠ x}

/-- The free commutative monoid on the non-section points. -/
abbrev conclusion_cmon_externalization_initial_prime_register_free_register
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Type u :=
  Multiset D.conclusion_cmon_externalization_initial_prime_register_nonsection

/-- The canonical generator of the free register. -/
def conclusion_cmon_externalization_initial_prime_register_generator
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v})
    (x : D.conclusion_cmon_externalization_initial_prime_register_nonsection) :
    D.conclusion_cmon_externalization_initial_prime_register_free_register :=
  {x}

/-- Extend a generator assignment uniquely to the free commutative monoid. -/
def conclusion_cmon_externalization_initial_prime_register_lift
    {D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}} {M : Type u}
    [AddCommMonoid M]
    (g : D.conclusion_cmon_externalization_initial_prime_register_nonsection → M) :
    D.conclusion_cmon_externalization_initial_prime_register_free_register →+ M where
  toFun s := (s.map g).sum
  map_zero' := by simp
  map_add' s t := by simp [Multiset.map_add, Multiset.sum_add]

@[simp]
lemma conclusion_cmon_externalization_initial_prime_register_lift_generator
    {D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}} {M : Type u}
    [AddCommMonoid M]
    (g : D.conclusion_cmon_externalization_initial_prime_register_nonsection → M)
    (x : D.conclusion_cmon_externalization_initial_prime_register_nonsection) :
    conclusion_cmon_externalization_initial_prime_register_lift g
        (D.conclusion_cmon_externalization_initial_prime_register_generator x) = g x := by
  simp [conclusion_cmon_externalization_initial_prime_register_lift,
    conclusion_cmon_externalization_initial_prime_register_generator]

lemma conclusion_cmon_externalization_initial_prime_register_lift_unique
    {D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}} {M : Type u}
    [AddCommMonoid M]
    (g : D.conclusion_cmon_externalization_initial_prime_register_nonsection → M)
    (φ :
      D.conclusion_cmon_externalization_initial_prime_register_free_register →+ M)
    (hφ :
      ∀ x : D.conclusion_cmon_externalization_initial_prime_register_nonsection,
        φ (D.conclusion_cmon_externalization_initial_prime_register_generator x) = g x) :
    φ = conclusion_cmon_externalization_initial_prime_register_lift g := by
  apply AddMonoidHom.ext
  intro s
  induction s using Multiset.induction_on with
  | empty =>
      simp [conclusion_cmon_externalization_initial_prime_register_lift]
  | cons x s ih =>
      have hx : φ ({x} : Multiset D.conclusion_cmon_externalization_initial_prime_register_nonsection) =
          g x := by
        simpa [conclusion_cmon_externalization_initial_prime_register_generator] using hφ x
      calc
        φ (x ::ₘ s) = φ ({x} + s) := by rw [Multiset.singleton_add]
        _ = φ {x} + φ s := by rw [map_add]
        _ = g x + (conclusion_cmon_externalization_initial_prime_register_lift g) s := by
          rw [hx, ih]
        _ = (conclusion_cmon_externalization_initial_prime_register_lift g) ({x} + s) := by
          rw [map_add]
          simp [conclusion_cmon_externalization_initial_prime_register_lift]
        _ = (conclusion_cmon_externalization_initial_prime_register_lift g) (x ::ₘ s) := by
          rw [Multiset.singleton_add]

/-- The section makes the projection onto the base object surjective. -/
def conclusion_cmon_externalization_initial_prime_register_projection_surjective
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Prop :=
  Function.Surjective D.conclusion_cmon_externalization_initial_prime_register_projection

/-- Initial morphism property of the free register. -/
def conclusion_cmon_externalization_initial_prime_register_initial_morphism_property
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Prop :=
  ∀ {M : Type u} [AddCommMonoid M],
    ∀ g : D.conclusion_cmon_externalization_initial_prime_register_nonsection → M,
      ∃! φ : D.conclusion_cmon_externalization_initial_prime_register_free_register →+ M,
        ∀ x : D.conclusion_cmon_externalization_initial_prime_register_nonsection,
          φ (D.conclusion_cmon_externalization_initial_prime_register_generator x) = g x

/-- If the generators embed into a countable prime register, so does the free register. -/
def conclusion_cmon_externalization_initial_prime_register_countable_prime_embedding
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Prop :=
  Nonempty
      (D.conclusion_cmon_externalization_initial_prime_register_nonsection ↪ ℕ) →
    Nonempty
      (D.conclusion_cmon_externalization_initial_prime_register_free_register ↪ Multiset ℕ)

end conclusion_cmon_externalization_initial_prime_register_data

/-- Concrete statement for
`thm:conclusion-cmon-externalization-initial-prime-register`. -/
def conclusion_cmon_externalization_initial_prime_register_statement
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) : Prop :=
  D.conclusion_cmon_externalization_initial_prime_register_projection_surjective ∧
    Function.RightInverse
      D.conclusion_cmon_externalization_initial_prime_register_section
      D.conclusion_cmon_externalization_initial_prime_register_projection ∧
    D.conclusion_cmon_externalization_initial_prime_register_initial_morphism_property ∧
    D.conclusion_cmon_externalization_initial_prime_register_countable_prime_embedding

/-- Paper label: `thm:conclusion-cmon-externalization-initial-prime-register`. -/
theorem paper_conclusion_cmon_externalization_initial_prime_register
    (D : conclusion_cmon_externalization_initial_prime_register_data.{u, v}) :
    conclusion_cmon_externalization_initial_prime_register_statement D := by
  refine ⟨?_, D.conclusion_cmon_externalization_initial_prime_register_section_right_inverse,
    ?_, ?_⟩
  · intro y
    exact ⟨D.conclusion_cmon_externalization_initial_prime_register_section y,
      D.conclusion_cmon_externalization_initial_prime_register_section_right_inverse y⟩
  · intro M _ g
    refine ⟨
      D.conclusion_cmon_externalization_initial_prime_register_lift g,
      ?_, ?_⟩
    · intro x
      simp
    · intro φ hφ
      exact D.conclusion_cmon_externalization_initial_prime_register_lift_unique g φ hφ
  · rintro ⟨e⟩
    exact ⟨
      { toFun := fun s => s.map e
        inj' := fun s t hst => Multiset.map_injective e.injective hst }⟩

end Omega.Conclusion
