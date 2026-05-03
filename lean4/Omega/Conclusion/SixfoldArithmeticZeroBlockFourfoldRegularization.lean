import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sixfold-arithmetic-zero-block-fourfold-regularization`.
If a zero-block lower bound is raised from `g` to `z`, the four tail bounds propagate back to
the original block parameter by monotonicity, while the collision estimate follows from
division by the positive mass scale. -/
theorem paper_conclusion_sixfold_arithmetic_zero_block_fourfold_regularization
    {M g z Col gap S D Dbar : ℝ} {tailGap tailS tailD : ℝ → ℝ}
    (hM : 0 < M) (hzero : g ≤ z) (hCol : Col ≤ 1 - z / M) (hgap : gap ≤ tailGap z)
    (hS : S ≤ tailS z) (hD : D - Dbar ≤ tailD z)
    (hgap_mono : ∀ z', g ≤ z' → tailGap z' ≤ tailGap g)
    (hS_mono : ∀ z', g ≤ z' → tailS z' ≤ tailS g)
    (hD_mono : ∀ z', g ≤ z' → tailD z' ≤ tailD g) :
    Col ≤ 1 - g / M ∧ gap ≤ tailGap g ∧ S ≤ tailS g ∧ D - Dbar ≤ tailD g := by
  have hdiv : g / M ≤ z / M := div_le_div_of_nonneg_right hzero hM.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hCol.trans (by linarith)
  · exact hgap.trans (hgap_mono z hzero)
  · exact hS.trans (hS_mono z hzero)
  · exact hD.trans (hD_mono z hzero)

end Omega.Conclusion
