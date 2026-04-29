import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The logarithmic constant term in the asymptotic expansion of `log N_{δ,w}(E)`. -/
noncomputable def boundary1FormConstantTerm
    (r_f : Nat) (E totalWeightLog kirchhoffLog : ℝ) : ℝ :=
  (r_f : ℝ) / 2 * Real.log E - totalWeightLog / 2 - kirchhoffLog / 2

/-- The determinant bonus extracted from the Hadamard comparison
`log τ_{1/w}(B_f) ≤ ∑ log C_t`. -/
noncomputable def determinantBonus (treeCutLog kirchhoffLog : ℝ) : ℝ :=
  (treeCutLog - kirchhoffLog) / 2

/-- The split form of the same constant term, separating the treewise cut contribution from
the determinant bonus. -/
noncomputable def boundary1FormSplitTerm
    (r_f : Nat) (E totalWeightLog treeCutLog kirchhoffLog : ℝ) : ℝ :=
  (r_f : ℝ) / 2 * Real.log E - totalWeightLog / 2 - treeCutLog / 2 +
    determinantBonus treeCutLog kirchhoffLog

/-- Paper-facing wrapper for the cut/determinant splitting of the boundary `1`-form counting
constant term.
    thm:conclusion-boundary-1form-cut-determinant-splitting -/
theorem paper_conclusion_boundary_1form_cut_determinant_splitting
    (r_f : Nat) (E totalWeightLog treeCutLog kirchhoffLog : ℝ)
    (orthogonal : Prop)
    (hHadamard : kirchhoffLog ≤ treeCutLog)
    (hCriterion : determinantBonus treeCutLog kirchhoffLog = 0 ↔ orthogonal) :
    boundary1FormConstantTerm r_f E totalWeightLog kirchhoffLog =
      boundary1FormSplitTerm r_f E totalWeightLog treeCutLog kirchhoffLog ∧
    0 ≤ determinantBonus treeCutLog kirchhoffLog ∧
    (determinantBonus treeCutLog kirchhoffLog = 0 ↔ orthogonal) := by
  refine ⟨?_, ?_, hCriterion⟩
  · unfold boundary1FormConstantTerm boundary1FormSplitTerm determinantBonus
    ring
  · unfold determinantBonus
    linarith

/-- Paper label: `cor:conclusion-treewise-cut-proxy-misses-determinant-layer`. -/
theorem paper_conclusion_treewise_cut_proxy_misses_determinant_layer
    {logN proxy bonus : ℝ} (hdecomp : logN = proxy + bonus) (hbonus : 0 < bonus) :
    proxy < logN := by
  linarith

end Omega.Conclusion
