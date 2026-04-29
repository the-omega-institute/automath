import Mathlib.Tactic

namespace Omega.Conclusion

/-- The number of window-6 fold-bin fibers with multiplicity at least `2`. -/
def conclusion_foldbin_gauge_schur_multiplier_rank_N2 : Nat := 21

/-- The number of window-6 fold-bin fibers with multiplicity at least `4`. -/
def conclusion_foldbin_gauge_schur_multiplier_rank_N4 : Nat := 9

/-- The `F₂`-rank obtained from the Schur multiplier rank formula. -/
def conclusion_foldbin_gauge_schur_multiplier_rank_rank : Nat :=
  conclusion_foldbin_gauge_schur_multiplier_rank_N4 +
    Nat.choose conclusion_foldbin_gauge_schur_multiplier_rank_N2 2

/-- Paper label: `thm:conclusion-foldbin-gauge-schur-multiplier-rank`.
The window-6 fiber counts `N₂ = 21` and `N₄ = 9` give rank
`N₄ + choose N₂ 2 = 219`. -/
def conclusion_foldbin_gauge_schur_multiplier_rank_statement : Prop :=
  conclusion_foldbin_gauge_schur_multiplier_rank_N2 = 21 ∧
    conclusion_foldbin_gauge_schur_multiplier_rank_N4 = 9 ∧
    conclusion_foldbin_gauge_schur_multiplier_rank_rank =
      conclusion_foldbin_gauge_schur_multiplier_rank_N4 +
        Nat.choose conclusion_foldbin_gauge_schur_multiplier_rank_N2 2 ∧
    conclusion_foldbin_gauge_schur_multiplier_rank_rank = 219

/-- Paper label: `thm:conclusion-foldbin-gauge-schur-multiplier-rank`. -/
theorem paper_conclusion_foldbin_gauge_schur_multiplier_rank :
    conclusion_foldbin_gauge_schur_multiplier_rank_statement := by
  unfold conclusion_foldbin_gauge_schur_multiplier_rank_statement
    conclusion_foldbin_gauge_schur_multiplier_rank_rank
    conclusion_foldbin_gauge_schur_multiplier_rank_N2
    conclusion_foldbin_gauge_schur_multiplier_rank_N4
  norm_num [Nat.choose]

end Omega.Conclusion
