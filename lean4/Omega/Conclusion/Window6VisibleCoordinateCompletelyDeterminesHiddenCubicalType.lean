import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-visible-coordinate-completely-determines-hidden-cubical-type`. The
hidden cubical type is the three-step function on `Fin 21` with breakpoints at `8` and `12`. -/
theorem paper_conclusion_window6_visible_coordinate_completely_determines_hidden_cubical_type
    (V : Fin 21) :
    let η := if V.1 ≤ 8 then (4 : ℕ) else if V.1 ≤ 12 then 3 else 2
    (η = 4 ↔ V.1 ≤ 8) ∧ (η = 3 ↔ 9 ≤ V.1 ∧ V.1 ≤ 12) ∧ (η = 2 ↔ 13 ≤ V.1) := by
  dsimp
  by_cases h8 : V.1 ≤ 8
  · have hnot9 : ¬ 9 ≤ V.1 := by omega
    have hnot13 : ¬ 13 ≤ V.1 := by omega
    simp [h8, hnot9, hnot13]
  · by_cases h12 : V.1 ≤ 12
    · have h9 : 9 ≤ V.1 := by omega
      have hnot13 : ¬ 13 ≤ V.1 := by omega
      simp [h8, h12, h9, hnot13]
    · have h13 : 13 ≤ V.1 := by omega
      simp [h8, h12, h13]

end Omega.Conclusion
