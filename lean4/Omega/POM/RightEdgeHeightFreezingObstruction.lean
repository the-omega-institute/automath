import Omega.POM.SpectrumRightEdgeSupportFunction

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-right-edge-height-freezing-obstruction`. -/
theorem paper_pom_right_edge_height_freezing_obstruction
    (alphaStar hStar : ℝ) (phases : List (ℝ × ℝ))
    (hcontains : (alphaStar, hStar) ∈ phases) (a : ℕ) (_ha : 1 ≤ a) :
    hStar ≤ pom_spectrum_right_edge_support_function_gap alphaStar phases (a : ℝ) ∧
      (0 < hStar →
        0 < pom_spectrum_right_edge_support_function_gap alphaStar phases (a : ℝ)) := by
  have hphase :
      hStar + (a : ℝ) * alphaStar ≤
        pom_spectrum_right_edge_support_function_pressure phases (a : ℝ) := by
    induction phases with
    | nil =>
        simp at hcontains
    | cons phase phases ih =>
        simp only [List.mem_cons] at hcontains
        simp only [pom_spectrum_right_edge_support_function_pressure, List.foldr_cons]
        rcases hcontains with hhead | htail
        · subst hhead
          exact le_max_left _ _
        · exact le_trans (ih htail) (le_max_right _ _)
  have hgap : hStar ≤
      pom_spectrum_right_edge_support_function_gap alphaStar phases (a : ℝ) := by
    unfold pom_spectrum_right_edge_support_function_gap
    linarith
  exact ⟨hgap, fun hpos => lt_of_lt_of_le hpos hgap⟩

end

end Omega.POM
