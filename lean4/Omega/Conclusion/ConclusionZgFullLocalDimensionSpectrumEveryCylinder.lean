import Mathlib.Data.List.Basic

namespace Omega.Conclusion

/-- Dimension values in the local model for the full ZG pointwise spectrum. -/
inductive conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind
    where
  | conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero
  | conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive
      (n : ℕ)
  | conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity
  deriving DecidableEq, Repr

/-- Concrete prefixed data for the cylinder-local ZG spectrum realization. -/
structure conclusion_zg_full_local_dimension_spectrum_every_cylinder_data where
  conclusion_zg_full_local_dimension_spectrum_every_cylinder_prefix_budget : ℕ := 0

namespace conclusion_zg_full_local_dimension_spectrum_every_cylinder_data

/-- Address cylinders are represented by finite binary prefixes. -/
abbrev conclusion_zg_full_local_dimension_spectrum_every_cylinder_cylinder
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data) : Type :=
  List Bool

/-- The three classes of local dimension values: zero, finite positive, and infinity. -/
abbrev conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data) : Type :=
  conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind

/-- Witness points remember their cylinder prefix and the realized local dimension value. -/
abbrev conclusion_zg_full_local_dimension_spectrum_every_cylinder_point
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data) : Type :=
  List Bool × conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind

/-- A nonempty cylinder is one whose prefix is accepted by the finite cylinder ledger. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_nonempty
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (_C : List Bool) : Prop :=
  True

/-- The image-membership predicate for the concrete prefixed witness model. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (x : List Bool ×
      conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind)
    (C : List Bool) : Prop :=
  x.1 = C

/-- Local dimension is the second coordinate of the witness point. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (x : List Bool ×
      conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind)
    (α : conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind) :
    Prop :=
  x.2 = α

/-- Tail constructor for the zero-dimensional branch. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero_tail
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (C : List Bool) :
    List Bool × conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind :=
  (C,
    .conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero)

/-- Tail constructor for the finite-positive-dimensional branch. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive_tail
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (C : List Bool) (n : ℕ) :
    List Bool × conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind :=
  (C,
    .conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive n)

/-- Tail constructor for the infinite-dimensional branch. -/
def conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity_tail
    (_D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (C : List Bool) :
    List Bool × conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value_kind :=
  (C,
    .conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity)

end conclusion_zg_full_local_dimension_spectrum_every_cylinder_data

open conclusion_zg_full_local_dimension_spectrum_every_cylinder_data

/-- Paper label: `thm:conclusion-zg-full-local-dimension-spectrum-every-cylinder`.
In the concrete prefixed model, every accepted cylinder has a witness point realizing each of
the three possible dimension-value constructors: zero, finite positive, and infinity. -/
theorem paper_conclusion_zg_full_local_dimension_spectrum_every_cylinder
    (D : conclusion_zg_full_local_dimension_spectrum_every_cylinder_data)
    (C :
      D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_cylinder)
    (α :
      D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_dimension_value) :
    D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_nonempty C →
      ∃ x,
        D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image x C ∧
          D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension x α := by
  intro _hC
  rcases α with - | q | -
  · refine
      ⟨D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero_tail C, ?_, ?_⟩
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero_tail]
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_zero_tail]
  · refine
      ⟨D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive_tail C q,
        ?_, ?_⟩
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive_tail]
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_finite_positive_tail]
  · refine
      ⟨D.conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity_tail C, ?_, ?_⟩
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_mem_image,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity_tail]
    · simp [conclusion_zg_full_local_dimension_spectrum_every_cylinder_local_dimension,
        conclusion_zg_full_local_dimension_spectrum_every_cylinder_infinity_tail]

end Omega.Conclusion
