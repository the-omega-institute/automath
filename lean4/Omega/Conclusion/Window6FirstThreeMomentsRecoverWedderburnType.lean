import Mathlib.Tactic
import Omega.Conclusion.Window6ThreeMomentSpectrumInversion

namespace Omega.Conclusion

/-- Recover the window-`6` Wedderburn multiplicities from the first three moments.
    thm:conclusion-window6-first-three-moments-recover-wedderburn-type -/
theorem paper_conclusion_window6_first_three_moments_recover_wedderburn_type
    {n2 n3 n4 : ℕ}
    (h0 : n2 + n3 + n4 = 21)
    (h1 : 2 * n2 + 3 * n3 + 4 * n4 = 64)
    (h2 : 4 * n2 + 9 * n3 + 16 * n4 = 212) :
    n2 = 8 ∧ n3 = 4 ∧ n4 = 9 := by
  have h0z : ((n2 : ℤ) + n3 + n4) = 21 := by
    exact_mod_cast h0
  have h1z : (2 : ℤ) * n2 + 3 * n3 + 4 * n4 = 64 := by
    exact_mod_cast h1
  have h2z : (4 : ℤ) * n2 + 9 * n3 + 16 * n4 = 212 := by
    exact_mod_cast h2
  rcases
      paper_conclusion_window6_three_moment_spectrum_inversion
        21 64 212 (n2 : ℤ) n3 n4 h0z.symm h1z.symm h2z.symm
    with ⟨hn2, hn3, hn4⟩
  norm_num at hn2 hn3 hn4
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hn2
  · exact_mod_cast hn3
  · exact_mod_cast hn4

end Omega.Conclusion
