namespace Omega.Zeta

/-- Paper label: `cor:xi-q5-unsolvable-by-radicals`. -/
theorem paper_xi_q5_unsolvable_by_radicals
    (q5HasGaloisS5 q5SolvableByRadicals : Prop)
    (hS5 : q5HasGaloisS5)
    (hS5_not_solvable : q5HasGaloisS5 → ¬ q5SolvableByRadicals) :
    ¬ q5SolvableByRadicals := by
  exact hS5_not_solvable hS5

end Omega.Zeta
