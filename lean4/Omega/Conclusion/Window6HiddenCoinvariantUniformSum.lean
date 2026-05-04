import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-coinvariant-uniform-sum`. -/
theorem paper_conclusion_window6_hidden_coinvariant_uniform_sum
    (hilbertFactorization independentUniformSum palindromicSymmetry : Prop)
    (hHilbert : hilbertFactorization)
    (hIndependent : hilbertFactorization -> independentUniformSum)
    (hSymm : hilbertFactorization -> palindromicSymmetry) :
    independentUniformSum ∧ ((21 : ℚ) / 2 + 13 + 9 * 3 / 2 = 37) ∧
      ((21 : ℚ) / 4 + 13 * 2 / 3 + 9 * 5 / 4 = 151 / 6) ∧
        palindromicSymmetry := by
  refine ⟨hIndependent hHilbert, ?_, ?_, hSymm hHilbert⟩ <;> norm_num

end Omega.Conclusion
