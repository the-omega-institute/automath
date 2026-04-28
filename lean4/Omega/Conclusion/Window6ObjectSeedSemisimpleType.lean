import Mathlib.Tactic
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-object-seed-fixes-unlabelled-semisimple-type-up-to-block-permutation`. -/
theorem paper_conclusion_window6_object_seed_fixes_unlabelled_semisimple_type_up_to_block_permutation
    {n2 n3 n4 : ℕ}
    (h0 : n2 + n3 + n4 = 21)
    (h1 : 2 * n2 + 3 * n3 + 4 * n4 = 64)
    (h2 : 4 * n2 + 9 * n3 + 16 * n4 = 212) :
    n2 = 8 ∧ n3 = 4 ∧ n4 = 9 := by
  exact paper_conclusion_window6_first_three_moments_recover_wedderburn_type h0 h1 h2

end Omega.Conclusion
