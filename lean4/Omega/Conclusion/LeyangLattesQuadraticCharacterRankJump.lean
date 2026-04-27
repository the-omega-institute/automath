import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-lattes-quadratic-character-rank-jump`. The visible
numeric jump from the Boolean sign cube of rank two to rank four has nontrivial character counts
`2^2 - 1 = 3` and `2^4 - 1 = 15`. -/
theorem paper_conclusion_leyang_lattes_quadratic_character_rank_jump :
    Fintype.card (Fin 2 → Bool) - 1 = 3 ∧ Fintype.card (Fin 4 → Bool) - 1 = 15 := by
  norm_num [Fintype.card_fun]

end Omega.Conclusion
