import Omega.Conclusion.Window6FiberGaugeLaplacianSpectrum

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-hidden-triple-fortythree-lock`. -/
theorem paper_conclusion_window6_hidden_triple_fortythree_lock :
    (21 + 13 + 9 = 43) ∧
      conclusion_window6_fiber_gauge_laplacian_spectral_functions_zeta_zero = 43 ∧
        (∃ factors : List ℕ,
          factors = List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4 ∧
            factors.length = 21 ∧ (factors.map (fun d => d - 1)).sum = 43) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num
  · exact paper_conclusion_window6_fiber_gauge_laplacian_spectral_functions.2.2.1
  · refine ⟨List.replicate 8 2 ++ List.replicate 4 3 ++ List.replicate 9 4, rfl, ?_, ?_⟩
    · norm_num
    · norm_num

end Omega.Conclusion
