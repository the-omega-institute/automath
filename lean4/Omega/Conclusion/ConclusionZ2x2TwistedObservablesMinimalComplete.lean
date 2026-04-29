import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The four hidden sectors are the two-bit group `Z/2 x Z/2`. -/
abbrev conclusion_z2x2_twisted_observables_minimal_complete_sector := Fin 2 × Fin 2

/-- Concrete data for the four-sector twisted-observable reconstruction problem. -/
structure conclusion_z2x2_twisted_observables_minimal_complete_data where
  signal : conclusion_z2x2_twisted_observables_minimal_complete_sector → ℚ

/-- The Walsh sign attached to a character and a sector. -/
def conclusion_z2x2_twisted_observables_minimal_complete_twist
    (χ s : conclusion_z2x2_twisted_observables_minimal_complete_sector) : ℚ :=
  if (χ.1.val * s.1.val + χ.2.val * s.2.val) % 2 = 0 then 1 else -1

/-- The four Walsh-twisted observations of a signal on the four sectors. -/
def conclusion_z2x2_twisted_observables_minimal_complete_observable
    (f : conclusion_z2x2_twisted_observables_minimal_complete_sector → ℚ)
    (χ : conclusion_z2x2_twisted_observables_minimal_complete_sector) : ℚ :=
  ∑ s : conclusion_z2x2_twisted_observables_minimal_complete_sector,
    conclusion_z2x2_twisted_observables_minimal_complete_twist χ s * f s

/-- Inversion from the four Walsh-twisted observations. -/
def conclusion_z2x2_twisted_observables_minimal_complete_inversion
    (f : conclusion_z2x2_twisted_observables_minimal_complete_sector → ℚ) : Prop :=
  ∀ s : conclusion_z2x2_twisted_observables_minimal_complete_sector,
    (1 / 4 : ℚ) *
        ∑ χ : conclusion_z2x2_twisted_observables_minimal_complete_sector,
          conclusion_z2x2_twisted_observables_minimal_complete_twist χ s *
            conclusion_z2x2_twisted_observables_minimal_complete_observable f χ =
      f s

/-- Fewer than four labels cannot separate all four sectors. -/
def conclusion_z2x2_twisted_observables_minimal_complete_minimality : Prop :=
  ∀ n < 4,
    ¬ ∃ encode : conclusion_z2x2_twisted_observables_minimal_complete_sector → Fin n,
      Function.Injective encode

/-- Concrete statement: the four Walsh observations invert the four-sector signal, and the
four observations are cardinally minimal. -/
def conclusion_z2x2_twisted_observables_minimal_complete_statement
    (D : conclusion_z2x2_twisted_observables_minimal_complete_data) : Prop :=
  conclusion_z2x2_twisted_observables_minimal_complete_inversion D.signal ∧
    conclusion_z2x2_twisted_observables_minimal_complete_minimality

lemma conclusion_z2x2_twisted_observables_minimal_complete_inversion_holds
    (f : conclusion_z2x2_twisted_observables_minimal_complete_sector → ℚ) :
    conclusion_z2x2_twisted_observables_minimal_complete_inversion f := by
  rintro ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Fintype.sum_prod_type,
      conclusion_z2x2_twisted_observables_minimal_complete_observable,
      conclusion_z2x2_twisted_observables_minimal_complete_twist, Fin.sum_univ_two] <;>
    ring_nf

lemma conclusion_z2x2_twisted_observables_minimal_complete_card_sector :
    Fintype.card conclusion_z2x2_twisted_observables_minimal_complete_sector = 4 := by
  simp [conclusion_z2x2_twisted_observables_minimal_complete_sector]

lemma conclusion_z2x2_twisted_observables_minimal_complete_minimality_holds :
    conclusion_z2x2_twisted_observables_minimal_complete_minimality := by
  intro n hn hencode
  rcases hencode with ⟨encode, hencode⟩
  have hcard :=
    Fintype.card_le_of_injective
      (α := conclusion_z2x2_twisted_observables_minimal_complete_sector) encode hencode
  rw [conclusion_z2x2_twisted_observables_minimal_complete_card_sector] at hcard
  simp at hcard
  omega

/-- Paper label: `thm:conclusion-z2x2-twisted-observables-minimal-complete`. -/
theorem paper_conclusion_z2x2_twisted_observables_minimal_complete
    (D : conclusion_z2x2_twisted_observables_minimal_complete_data) :
    conclusion_z2x2_twisted_observables_minimal_complete_statement D := by
  exact ⟨conclusion_z2x2_twisted_observables_minimal_complete_inversion_holds D.signal,
    conclusion_z2x2_twisted_observables_minimal_complete_minimality_holds⟩

end Omega.Conclusion
