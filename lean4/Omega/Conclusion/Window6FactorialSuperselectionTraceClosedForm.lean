import Mathlib
import Omega.Conclusion.Window6CanonicalMicrostateBoundaryCharacterCollapse

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

def conclusion_window6_factorial_superselection_trace_closed_form_E64 (t : ℂ) : ℂ :=
  Finset.sum (Finset.range 64) fun n => t ^ n / (Nat.factorial n : ℂ)

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps1 (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (t ^ 14 / (Nat.factorial 14 : ℂ) + t ^ 48 / (Nat.factorial 48 : ℂ))

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps2 (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (t ^ 17 / (Nat.factorial 17 : ℂ) + t ^ 51 / (Nat.factorial 51 : ℂ))

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps3 (t : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (t ^ 19 / (Nat.factorial 19 : ℂ) + t ^ 53 / (Nat.factorial 53 : ℂ))

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps12 (_t : ℂ) : ℂ := 0

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps13 (_t : ℂ) : ℂ := 0

def conclusion_window6_factorial_superselection_trace_closed_form_Zeps23 (_t : ℂ) : ℂ := 0

def conclusion_window6_factorial_superselection_trace_closed_form_Zdelta (_t : ℂ) : ℂ := 0

def conclusion_window6_factorial_superselection_trace_closed_form_Ztrivial (t : ℂ) : ℂ :=
  conclusion_window6_factorial_superselection_trace_closed_form_E64 t -
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps1 t -
      conclusion_window6_factorial_superselection_trace_closed_form_Zeps2 t -
        conclusion_window6_factorial_superselection_trace_closed_form_Zeps3 t

def conclusion_window6_factorial_superselection_trace_closed_form_statement (t : ℂ) : Prop :=
  conclusion_window6_factorial_superselection_trace_closed_form_Zeps1 t =
      (1 / 2 : ℂ) * (t ^ 14 / (Nat.factorial 14 : ℂ) + t ^ 48 / (Nat.factorial 48 : ℂ)) ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps2 t =
      (1 / 2 : ℂ) * (t ^ 17 / (Nat.factorial 17 : ℂ) + t ^ 51 / (Nat.factorial 51 : ℂ)) ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps3 t =
      (1 / 2 : ℂ) * (t ^ 19 / (Nat.factorial 19 : ℂ) + t ^ 53 / (Nat.factorial 53 : ℂ)) ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps12 t = 0 ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps13 t = 0 ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps23 t = 0 ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Zdelta t = 0 ∧
    conclusion_window6_factorial_superselection_trace_closed_form_Ztrivial t =
      conclusion_window6_factorial_superselection_trace_closed_form_E64 t -
        conclusion_window6_factorial_superselection_trace_closed_form_Zeps1 t -
          conclusion_window6_factorial_superselection_trace_closed_form_Zeps2 t -
            conclusion_window6_factorial_superselection_trace_closed_form_Zeps3 t ∧
    window6CanonicalMicrostateBoundaryCharacterMultiplicity χ111 = 0 ∧
    window6CanonicalMicrostateBoundaryCharacterMultiplicity χ110 = 0 ∧
    window6CanonicalMicrostateBoundaryCharacterMultiplicity χ101 = 0 ∧
    window6CanonicalMicrostateBoundaryCharacterMultiplicity χ011 = 0

theorem paper_conclusion_window6_factorial_superselection_trace_closed_form (t : ℂ) :
    conclusion_window6_factorial_superselection_trace_closed_form_statement t := by
  rcases paper_conclusion_window6_canonical_microstate_boundary_character_collapse with
    ⟨_, _, _, _, _, _, _, _, h111, h110, h101, h011⟩
  simp [conclusion_window6_factorial_superselection_trace_closed_form_statement,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps1,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps2,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps3,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps12,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps13,
    conclusion_window6_factorial_superselection_trace_closed_form_Zeps23,
    conclusion_window6_factorial_superselection_trace_closed_form_Zdelta,
    conclusion_window6_factorial_superselection_trace_closed_form_Ztrivial,
    h111, h110, h101, h011]

end

end Omega.Conclusion
