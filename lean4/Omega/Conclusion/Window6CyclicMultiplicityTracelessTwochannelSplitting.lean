import Mathlib.Tactic
import Omega.Conclusion.Window6B3C3AnisotropyRankDrop

namespace Omega.Conclusion

open Matrix

/-- Paper-facing traceless splitting of the cyclic multiplicity second moment into the two
anisotropic diagonal channels.
    thm:conclusion-window6-cyclic-multiplicity-traceless-twochannel-splitting -/
def Window6CyclicMultiplicityTracelessTwochannelSplitting (f2 f3 f4 : ℝ) : Prop :=
  let u := f4 - f2
  let v := f3 - f2
  Matrix.trace (window6WeightedMomentB f2 f3 f4) = 30 * f2 + 13 * u + 8 * v ∧
    window6WeightedMomentB f2 f3 f4 -
        (Matrix.trace (window6WeightedMomentB f2 f3 f4) / 3) •
          (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      (u / 3) • Matrix.diagonal ![(2 : ℝ), 5, -7] +
        ((4 * v) / 3) • Matrix.diagonal ![(1 : ℝ), -2, 1]

theorem paper_conclusion_window6_cyclic_multiplicity_traceless_twochannel_splitting
    (f2 f3 f4 : ℝ) : Window6CyclicMultiplicityTracelessTwochannelSplitting f2 f3 f4 := by
  dsimp [Window6CyclicMultiplicityTracelessTwochannelSplitting]
  have hM :
      window6WeightedMomentB f2 f3 f4 =
        Matrix.diagonal ![10 * f2 + 5 * (f4 - f2) + 4 * (f3 - f2), 10 * f2 + 6 * (f4 - f2),
          10 * f2 + 2 * (f4 - f2) + 4 * (f3 - f2)] := by
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
  have htrace :
      Matrix.trace (window6WeightedMomentB f2 f3 f4) =
        30 * f2 + 13 * (f4 - f2) + 8 * (f3 - f2) := by
    rw [hM]
    simp [Matrix.trace, Fin.sum_univ_three]
    ring_nf
  refine ⟨htrace, ?_⟩
  rw [hM]
  have htraceDiag :
      Matrix.trace
          (Matrix.diagonal
            ![10 * f2 + 5 * (f4 - f2) + 4 * (f3 - f2), 10 * f2 + 6 * (f4 - f2),
              10 * f2 + 2 * (f4 - f2) + 4 * (f3 - f2)] : Matrix (Fin 3) (Fin 3) ℝ) =
        30 * f2 + 13 * (f4 - f2) + 8 * (f3 - f2) := by
    simpa [hM] using htrace
  rw [htraceDiag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf

end Omega.Conclusion
