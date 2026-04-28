import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-window6-rational-homotopy-poincare`. -/
theorem paper_conclusion_foldbin_window6_rational_homotopy_poincare :
    ∃ factors : List ℕ,
      factors = List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4 ∧
        factors.length = 21 ∧ (factors.map (fun d => d - 1)).sum = 43 := by
  refine ⟨List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4, rfl, ?_, ?_⟩
  · norm_num
  · norm_num

end Omega.Conclusion
