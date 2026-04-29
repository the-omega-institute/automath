import Mathlib.Tactic
import Omega.Conclusion.Window6CyclicMultiplicityThreeparameterNormalform
import Omega.Conclusion.Window6CyclicMultiplicityTracelessTwochannelSplitting

namespace Omega.Conclusion

open Matrix

/-- Paper label:
`thm:conclusion-window6-cyclic-multiplicity-escort-unique-isotropy`. -/
theorem paper_conclusion_window6_cyclic_multiplicity_escort_unique_isotropy (q : ℕ) :
    (window6CyclicMultiplicityFirstMoment ((2 : ℝ) ^ q) ((3 : ℝ) ^ q) ((4 : ℝ) ^ q) = 0 ↔
      q = 0) ∧
    ((∃ a : ℝ,
      window6WeightedMomentB ((2 : ℝ) ^ q) ((3 : ℝ) ^ q) ((4 : ℝ) ^ q) =
        a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ↔ q = 0) := by
  constructor
  · constructor
    · intro h
      by_contra hq
      have hq_ne : q ≠ 0 := hq
      have hentry := congr_fun h (0 : Fin 3)
      simp [window6CyclicMultiplicityFirstMoment] at hentry
      have hlt : (2 : ℝ) ^ q < (4 : ℝ) ^ q := by
        exact pow_lt_pow_left₀ (by norm_num : (2 : ℝ) < 4) (by norm_num : (0 : ℝ) ≤ 2)
          hq_ne
      linarith
    · intro hq
      subst q
      simp [window6CyclicMultiplicityFirstMoment]
  · constructor
    · rintro ⟨a, hscalar⟩
      by_contra hq
      have hq_ne : q ≠ 0 := hq
      let f2 : ℝ := (2 : ℝ) ^ q
      let f3 : ℝ := (3 : ℝ) ^ q
      let f4 : ℝ := (4 : ℝ) ^ q
      have hdiag :
          window6WeightedMomentB f2 f3 f4 =
            Matrix.diagonal ![f2 + 4 * f3 + 5 * f4, 4 * f2 + 6 * f4,
              4 * f2 + 4 * f3 + 2 * f4] := by
        exact (paper_conclusion_window6_b3c3_anisotropy_rank_drop f2 f3 f4).1
      have hscalar' :
          window6WeightedMomentB f2 f3 f4 = a • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        simpa [f2, f3, f4] using hscalar
      have h12 :
          window6WeightedMomentB f2 f3 f4 (1 : Fin 3) (1 : Fin 3) =
            window6WeightedMomentB f2 f3 f4 (2 : Fin 3) (2 : Fin 3) := by
        calc
          window6WeightedMomentB f2 f3 f4 (1 : Fin 3) (1 : Fin 3) =
              (a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (1 : Fin 3) (1 : Fin 3) := by
                rw [hscalar']
          _ = a := by simp
          _ = (a • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (2 : Fin 3) (2 : Fin 3) := by
                simp
          _ = window6WeightedMomentB f2 f3 f4 (2 : Fin 3) (2 : Fin 3) := by
                rw [hscalar']
      have hpow_eq : (4 : ℝ) ^ q = (3 : ℝ) ^ q := by
        rw [hdiag] at h12
        simp [f2, f3, f4] at h12
        linarith
      have hlt : (3 : ℝ) ^ q < (4 : ℝ) ^ q := by
        exact pow_lt_pow_left₀ (by norm_num : (3 : ℝ) < 4) (by norm_num : (0 : ℝ) ≤ 3)
          hq_ne
      linarith
    · intro hq
      subst q
      refine ⟨10, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [window6WeightedMomentB, window6B3MomentQ2, window6B3MomentQ3, window6B3MomentQ4] <;>
        norm_num

end Omega.Conclusion
