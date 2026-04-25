import Omega.Conclusion.Window6ArbitraryMultiplicitySecondMomentRigidity
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-fixedwindow-shell-dual-completeness`. The first three
window-`6` moments rigidly recover the histogram `(8,4,9)`, while the diagonal second-moment data
recover the shell weights and are isotropic exactly in the constant-weight case. -/
theorem paper_conclusion_window6_fixedwindow_shell_dual_completeness :
    (∀ {n2 n3 n4 : ℕ},
      n2 + n3 + n4 = 21 →
        2 * n2 + 3 * n3 + 4 * n4 = 64 →
          4 * n2 + 9 * n3 + 16 * n4 = 212 →
            n2 = 8 ∧ n3 = 4 ∧ n4 = 9) ∧
      (∀ f2 f3 f4 : ℤ,
        let A := f2 + 4 * f3 + 5 * f4
        let B := 4 * f2 + 6 * f4
        let C := 4 * f2 + 4 * f3 + 2 * f4
        ((-2 * A + B + 2 * C) / 10 = f2 ∧
          (8 * A - 9 * B + 7 * C) / 60 = f3 ∧
          (4 * A + 3 * B - 4 * C) / 30 = f4 ∧
          ((A = B ∧ B = C) ↔ (f2 = f3 ∧ f3 = f4)))) := by
  refine ⟨?_, ?_⟩
  · intro n2 n3 n4 h0 h1 h2
    exact paper_conclusion_window6_first_three_moments_recover_wedderburn_type h0 h1 h2
  · intro f2 f3 f4
    dsimp
    have hA :
        -2 * (f2 + 4 * f3 + 5 * f4) + (4 * f2 + 6 * f4) + 2 * (4 * f2 + 4 * f3 + 2 * f4) =
          10 * f2 := by
      ring
    have hB :
        8 * (f2 + 4 * f3 + 5 * f4) - 9 * (4 * f2 + 6 * f4) +
            7 * (4 * f2 + 4 * f3 + 2 * f4) =
          60 * f3 := by
      ring
    have hC :
        4 * (f2 + 4 * f3 + 5 * f4) + 3 * (4 * f2 + 6 * f4) -
            4 * (4 * f2 + 4 * f3 + 2 * f4) =
          30 * f4 := by
      ring
    have hdivA : (10 : ℤ) ∣ 10 * f2 := dvd_mul_right 10 f2
    have hdivB : (60 : ℤ) ∣ 60 * f3 := dvd_mul_right 60 f3
    have hdivC : (30 : ℤ) ∣ 30 * f4 := dvd_mul_right 30 f4
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hA]
      have hcancelA : (10 * f2 / 10) * 10 = 10 * f2 := by
        simpa [mul_comm] using Int.ediv_mul_cancel hdivA
      nlinarith
    · rw [hB]
      have hcancelB : (60 * f3 / 60) * 60 = 60 * f3 := by
        simpa [mul_comm] using Int.ediv_mul_cancel hdivB
      nlinarith
    · rw [hC]
      have hcancelC : (30 * f4 / 30) * 30 = 30 * f4 := by
        simpa [mul_comm] using Int.ediv_mul_cancel hdivC
      nlinarith
    · simpa using paper_conclusion_window6_arbitrary_multiplicity_second_moment_rigidity f2 f3 f4

end Omega.Conclusion
