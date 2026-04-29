import Mathlib.Tactic
import Omega.Zeta.DerivedExactEntropySaturationExcludesMultidefect

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-defect-uniform-frontier-entropy-saturation-exclusion`. Exact
entropy saturation forces the derived Hankel rank to be at most one, contradicting any stable
defect lower bound of rank at least two. -/
theorem paper_conclusion_defect_uniform_frontier_entropy_saturation_exclusion {κ : Nat}
    (hκ : 2 ≤ κ) (mass δ phase : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j)
    (hδ : ∀ j, 0 < δ j) (hphase : ∀ j, |phase j| ≤ 1)
    (hgap : Omega.Zeta.xiEntropyGap mass δ = 0)
    (hrank :
      2 ≤ Matrix.rank
        (Omega.Zeta.derived_exact_entropy_saturation_excludes_multidefect_hankel κ mass δ
          phase)) :
    False := by
  have hrank_upper :
      Matrix.rank
          (Omega.Zeta.derived_exact_entropy_saturation_excludes_multidefect_hankel κ mass δ
            phase) ≤
        1 :=
    (Omega.Zeta.paper_derived_exact_entropy_saturation_excludes_multidefect mass δ phase hm hδ
      hphase hgap).2
  have : 0 < κ := lt_of_lt_of_le (by norm_num : 0 < 2) hκ
  omega

end Omega.Conclusion
