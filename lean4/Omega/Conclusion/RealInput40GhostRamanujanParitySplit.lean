import Mathlib.Tactic

namespace Omega.Conclusion

/-- Even branch of the single-atom ghost Ramanujan ray. -/
def conclusion_realinput40_ghost_ramanujan_parity_split_even_form
    (r : ℕ) (z u : ℚ) : ℚ :=
  2 * (u ^ (r / 2) * z ^ r) / (1 - u ^ (r / 2) * z ^ r)

/-- Odd branch of the single-atom ghost Ramanujan ray. -/
def conclusion_realinput40_ghost_ramanujan_parity_split_odd_form
    (r : ℕ) (z u : ℚ) : ℚ :=
  2 * (u ^ r * z ^ (2 * r)) / (1 - u ^ r * z ^ (2 * r))

/-- The single `(1,2,1)` atom ghost ray, split by parity of the divisor layer. -/
def conclusion_realinput40_ghost_ramanujan_parity_split_single_atom_ray
    (r : ℕ) (z u : ℚ) : ℚ :=
  if Even r then
    conclusion_realinput40_ghost_ramanujan_parity_split_even_form r z u
  else
    conclusion_realinput40_ghost_ramanujan_parity_split_odd_form r z u

/-- Concrete statement for the real-input `40` single-atom ghost Ramanujan parity split. -/
def conclusion_realinput40_ghost_ramanujan_parity_split_statement : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ z u : ℚ,
    (Even r →
      conclusion_realinput40_ghost_ramanujan_parity_split_single_atom_ray r z u =
        conclusion_realinput40_ghost_ramanujan_parity_split_even_form r z u) ∧
    (Odd r →
      conclusion_realinput40_ghost_ramanujan_parity_split_single_atom_ray r z u =
        conclusion_realinput40_ghost_ramanujan_parity_split_odd_form r z u)

/-- Paper label: `cor:conclusion-realinput40-ghost-ramanujan-parity-split`. -/
theorem paper_conclusion_realinput40_ghost_ramanujan_parity_split :
    conclusion_realinput40_ghost_ramanujan_parity_split_statement := by
  intro r _hr z u
  constructor
  · intro hEven
    simp [conclusion_realinput40_ghost_ramanujan_parity_split_single_atom_ray, hEven]
  · intro hOdd
    have hNotEven : ¬ Even r := by
      exact Nat.not_even_iff_odd.mpr hOdd
    simp [conclusion_realinput40_ghost_ramanujan_parity_split_single_atom_ray, hNotEven]

end Omega.Conclusion
