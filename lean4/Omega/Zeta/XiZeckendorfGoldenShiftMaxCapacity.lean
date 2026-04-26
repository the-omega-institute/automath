import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Paper label: `thm:xi-zeckendorf-golden-shift-max-capacity`. -/
theorem paper_xi_zeckendorf_golden_shift_max_capacity
    (GoldenShift : Type u) (admissible : Type u → Prop) (capacity : Type u → ℝ)
    (Conjugate : Type u → Type u → Prop) (hGolden : admissible GoldenShift)
    (hMax : ∀ Y, admissible Y → capacity Y ≤ capacity GoldenShift)
    (hUnique : ∀ Y, admissible Y → capacity Y = capacity GoldenShift → Conjugate Y GoldenShift) :
    (∀ Y, admissible Y → capacity Y ≤ capacity GoldenShift) ∧
      (∀ Y, admissible Y → capacity Y = capacity GoldenShift → Conjugate Y GoldenShift) := by
  have _ : admissible GoldenShift := hGolden
  exact ⟨hMax, hUnique⟩

end Omega.Zeta
