import Mathlib.Tactic
import Omega.Conclusion.Window6B3C3AnisotropyRankDrop

namespace Omega.Conclusion

open Matrix

/-- The first cyclic multiplicity moment in the pinned `B₃` frame. -/
def window6CyclicMultiplicityFirstMoment (f2 _f3 f4 : ℝ) : Fin 3 → ℝ :=
  ![f4 - f2, 0, 0]

/-- Paper-facing three-parameter normal form for the cyclic multiplicity first and second moments.
    thm:conclusion-window6-cyclic-multiplicity-threeparameter-normalform -/
def Window6CyclicMultiplicityThreeparameterNormalform (f2 f3 f4 : ℝ) : Prop :=
  let c := f2
  let u := f4 - f2
  let v := f3 - f2
  window6CyclicMultiplicityFirstMoment f2 f3 f4 = ![u, 0, 0] ∧
    window6WeightedMomentB f2 f3 f4 =
      Matrix.diagonal ![10 * c + 5 * u + 4 * v, 10 * c + 6 * u, 10 * c + 2 * u + 4 * v]

theorem paper_conclusion_window6_cyclic_multiplicity_threeparameter_normalform
    (f2 f3 f4 : ℝ) : Window6CyclicMultiplicityThreeparameterNormalform f2 f3 f4 := by
  dsimp [Window6CyclicMultiplicityThreeparameterNormalform]
  refine ⟨by simp [window6CyclicMultiplicityFirstMoment], ?_⟩
  calc
    window6WeightedMomentB f2 f3 f4 =
        Matrix.diagonal ![f2 + 4 * f3 + 5 * f4, 4 * f2 + 6 * f4, 4 * f2 + 4 * f3 + 2 * f4] := by
          exact (paper_conclusion_window6_b3c3_anisotropy_rank_drop f2 f3 f4).1
    _ = Matrix.diagonal
          ![10 * f2 + 5 * (f4 - f2) + 4 * (f3 - f2), 10 * f2 + 6 * (f4 - f2),
            10 * f2 + 2 * (f4 - f2) + 4 * (f3 - f2)] := by
          congr 1
          funext i
          fin_cases i <;> ring_nf

end Omega.Conclusion
