import Omega.Conclusion.QuadraticFieldRamification
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The first finite branch value over the quadratic field `Q(√89)`. -/
noncomputable def xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JPlus : ℝ :=
  -931 + 89 * Real.sqrt 89

/-- The conjugate finite branch value over the quadratic field `Q(√89)`. -/
noncomputable def xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JMinus : ℝ :=
  -931 - 89 * Real.sqrt 89

/-- The quadratic polynomial cutting out the two branch values. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadratic (T : ℝ) : ℝ :=
  T ^ 2 + 1862 * T + 161792

/-- The discriminant of the displayed quadratic polynomial. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_discriminant : ℤ :=
  1862 ^ 2 - 4 * 161792

/-- The quadratic-subfield fingerprint attached to the branch pair. -/
def xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadraticSubfieldDiscriminant : ℤ :=
  89

lemma xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadDisc_eq_eighty_nine_unique
    (d : ℤ) (h : Omega.Conclusion.QuadraticFieldRamification.quadDisc d = 89) : d = 89 := by
  by_cases hd : d % 4 = 1
  · simpa [Omega.Conclusion.QuadraticFieldRamification.quadDisc, hd] using h
  · have h' : 4 * d = 89 := by
      simpa [Omega.Conclusion.QuadraticFieldRamification.quadDisc, hd] using h
    have hmod := congrArg (fun z : ℤ => z % 4) h'
    norm_num at hmod

/-- Paper label: `prop:xi-terminal-zm-leyang-spectral-quartic-a-j-fib89-minpoly`. The two
explicit branch values are the roots of `T² + 1862 T + 161792`, its discriminant is `4 * 89^3`,
and the resulting quadratic-field fingerprint is exactly the one of `Q(√89)`. -/
theorem paper_xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly :
    (∀ T : ℝ,
      (T - xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JPlus) *
          (T - xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JMinus) =
        xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadratic T) ∧
      xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_discriminant = 4 * 89 ^ 3 ∧
      Omega.Conclusion.QuadraticFieldRamification.quadDisc
          xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadraticSubfieldDiscriminant =
        89 ∧
      ∀ d : ℤ,
        Omega.Conclusion.QuadraticFieldRamification.quadDisc d = 89 →
          d =
            xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadraticSubfieldDiscriminant := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T
    have hsqrt89 : (Real.sqrt 89) ^ 2 = (89 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    unfold xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JPlus
      xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_JMinus
      xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadratic
    ring_nf
    rw [hsqrt89]
    ring
  · norm_num [xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_discriminant]
  · simp [xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadraticSubfieldDiscriminant,
      Omega.Conclusion.QuadraticFieldRamification.quadDisc]
  · intro d hd
    simpa [xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadraticSubfieldDiscriminant]
      using
        xi_terminal_zm_leyang_spectral_quartic_a_j_fib89_minpoly_quadDisc_eq_eighty_nine_unique d hd

end Omega.Zeta
