import Mathlib.Tactic

namespace Omega.FiniteFieldEquationalSaturation.ContentBound

/-- A finite-support two-variable integer polynomial modelled by its finite coefficient table. -/
abbrev finite_field_content_bound_IntPoly2 := Fin 4 → ℤ

/-- Reduction is zero exactly when every stored integer coefficient vanishes modulo `p`. -/
def finite_field_content_bound_reducesToZero
    (p : Nat) (f : finite_field_content_bound_IntPoly2) : Prop :=
  ∀ i : Fin 4, p ∣ Int.natAbs (f i)

/-- The coefficient content is the gcd of the finite coefficient table. -/
def finite_field_content_bound_content (f : finite_field_content_bound_IntPoly2) : Nat :=
  Finset.univ.gcd fun i : Fin 4 => Int.natAbs (f i)

/-- thm:finite-field-content-bound -/
theorem paper_finite_field_content_bound
    (p : Nat) (f : finite_field_content_bound_IntPoly2) :
    finite_field_content_bound_reducesToZero p f ↔
      p ∣ finite_field_content_bound_content f := by
  simp [finite_field_content_bound_reducesToZero, finite_field_content_bound_content,
    Finset.dvd_gcd_iff]

end Omega.FiniteFieldEquationalSaturation.ContentBound
