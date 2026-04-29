import Mathlib

namespace Omega.Conclusion

open Matrix

/-- Partial `B₃` moment from the `d = 2` multiplicity class. -/
def window6B3MomentQ2 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![1, 4, 4]

/-- Partial `B₃` moment from the `d = 3` multiplicity class. -/
def window6B3MomentQ3 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![4, 0, 4]

/-- Partial `B₃` moment from the `d = 4` multiplicity class. -/
def window6B3MomentQ4 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![5, 6, 2]

/-- Partial `C₃` moment from the `d = 2` multiplicity class. -/
def window6C3MomentQ2 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![4, 4, 4]

/-- Partial `C₃` moment from the `d = 3` multiplicity class. -/
def window6C3MomentQ3 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![4, 0, 4]

/-- Partial `C₃` moment from the `d = 4` multiplicity class. -/
def window6C3MomentQ4 : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![8, 12, 8]

/-- Weighted second moment in the `B₃` normalization. -/
def window6WeightedMomentB (f2 f3 f4 : Real) : Matrix (Fin 3) (Fin 3) Real :=
  f2 • window6B3MomentQ2 + f3 • window6B3MomentQ3 + f4 • window6B3MomentQ4

/-- Weighted second moment in the `C₃` normalization. -/
def window6WeightedMomentC (f2 f3 f4 : Real) : Matrix (Fin 3) (Fin 3) Real :=
  f2 • window6C3MomentQ2 + f3 • window6C3MomentQ3 + f4 • window6C3MomentQ4

/-- Explicit diagonal formulas for the weighted `B₃/C₃` second moments.
    thm:conclusion-window6-b3c3-anisotropy-rank-drop -/
theorem paper_conclusion_window6_b3c3_anisotropy_rank_drop (f2 f3 f4 : Real) :
    window6WeightedMomentB f2 f3 f4 =
      Matrix.diagonal ![f2 + 4 * f3 + 5 * f4, 4 * f2 + 6 * f4, 4 * f2 + 4 * f3 + 2 * f4] /\
    window6WeightedMomentC f2 f3 f4 =
      Matrix.diagonal ![4 * f2 + 4 * f3 + 8 * f4, 4 * f2 + 12 * f4, 4 * f2 + 4 * f3 + 8 * f4] := by
  constructor
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [window6WeightedMomentB, window6B3MomentQ2, window6B3MomentQ3, window6B3MomentQ4] <;>
      ring
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [window6WeightedMomentC, window6C3MomentQ2, window6C3MomentQ3, window6C3MomentQ4] <;>
      ring

end Omega.Conclusion
