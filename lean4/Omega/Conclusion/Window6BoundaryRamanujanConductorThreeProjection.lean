import Mathlib.Tactic

namespace Omega.Conclusion

abbrev BoundaryQVector := Fin 3 → ℚ

/-- The cyclic `C₃` action on the boundary coordinates. -/
def sigma3 (x : BoundaryQVector) : BoundaryQVector :=
  ![x 1, x 2, x 0]

/-- The conductor-`3` Ramanujan average. -/
def ramanujanMean3 (x : BoundaryQVector) : ℚ :=
  (x 0 + x 1 + x 2) / 3

/-- The conductor-`3` Ramanujan projection onto the zero-sum plane. -/
def ramanujanProjection3 (x : BoundaryQVector) : BoundaryQVector :=
  ![x 0 - ramanujanMean3 x, x 1 - ramanujanMean3 x, x 2 - ramanujanMean3 x]

/-- `thm:conclusion-window6-boundary-ramanujan-conductor-three-projection` -/
theorem paper_conclusion_window6_boundary_ramanujan_conductor_three_projection
    (x : Fin 3 → ℚ) :
    let y := ramanujanProjection3 x
    y =
        ![x 0 - (x 0 + x 1 + x 2) / 3, x 1 - (x 0 + x 1 + x 2) / 3,
          x 2 - (x 0 + x 1 + x 2) / 3] ∧
      y 0 + y 1 + y 2 = 0 ∧ ramanujanProjection3 y = y := by
  dsimp [ramanujanProjection3, ramanujanMean3]
  refine ⟨rfl, ?_, ?_⟩
  · ring
  · ext i
    fin_cases i <;> ring_nf

end Omega.Conclusion
