import Mathlib.Tactic
import Omega.Conclusion.Window6ThreeLowOrderMomentsRigidifyFullSpectrum

namespace Omega.Conclusion

/-- The recovered window-`6` atomic moment sequence with support `{2,3,4}` and weights `(8,4,9)`. -/
def conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment (q : ℕ) : ℕ :=
  8 * 2 ^ q + 4 * 3 ^ q + 9 * 4 ^ q

/-- The cubic recurrence determined by the first four Toeplitz moments `c₀` through `c₃`. -/
def conclusion_window6_weyl_toeplitz_third_moment_sufficiency_recurs (q : ℕ) : Prop :=
  conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment (q + 3) =
    9 * conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment (q + 2) -
      26 * conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment (q + 1) +
        24 * conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment q

/-- Concrete third-moment sufficiency package for the window-`6` Weyl/Toeplitz model. -/
def conclusion_window6_weyl_toeplitz_third_moment_sufficiency_statement : Prop :=
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment 0 = 21 ∧
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment 1 = 64 ∧
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment 2 = 212 ∧
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment 3 = 748 ∧
    (∀ q : ℕ, conclusion_window6_weyl_toeplitz_third_moment_sufficiency_recurs q)

/-- Paper label: `cor:conclusion-window6-weyl-toeplitz-third-moment-sufficiency`.
The first four Toeplitz moments of the recovered three-atom window-`6` spectrum determine all
higher moments through the cubic recurrence with roots `2`, `3`, and `4`. -/
theorem paper_conclusion_window6_weyl_toeplitz_third_moment_sufficiency :
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_statement := by
  rcases
      paper_conclusion_window6_three_low_order_moments_rigidify_full_spectrum
        (n2 := 8) (n3 := 4) (n4 := 9) (by norm_num) (by norm_num) (by norm_num)
    with ⟨_, _, _, hrec⟩
  refine ⟨by norm_num [conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment],
    by norm_num [conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment],
    by norm_num [conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment],
    by norm_num [conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment], ?_⟩
  intro q
  unfold conclusion_window6_weyl_toeplitz_third_moment_sufficiency_recurs
    conclusion_window6_weyl_toeplitz_third_moment_sufficiency_moment
  simpa using hrec q

end Omega.Conclusion
