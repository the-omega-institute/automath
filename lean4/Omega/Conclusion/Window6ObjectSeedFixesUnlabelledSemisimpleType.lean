import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-object-seed-fixes-unlabelled-semisimple-type-up-to-block-permutation`. -/
theorem paper_conclusion_window6_object_seed_fixes_unlabelled_semisimple_type_up_to_block_permutation :
    (∀ a b c : ℕ,
      a + b + c = 21 →
        2 * a + 6 * b + 12 * c = 64 →
          4 * a + 9 * b + 16 * c = 212 → a = 8 ∧ b = 4 ∧ c = 9) ∧
      8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧ 8 + 4 + 9 = 21 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  intro a b c hsum hdim hsq
  omega

end Omega.Conclusion
