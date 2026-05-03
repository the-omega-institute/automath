import Omega.Conclusion.DyadicBoundaryPrimeshellBooleanDivisorTomography

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-dyadic-boundary-primeshell-composite-conductors-redundant`. -/
theorem paper_conclusion_dyadic_boundary_primeshell_composite_conductors_redundant
    (q boundary : Finset ℕ) :
    booleanPrimeShellCoefficient boundary q =
        q.prod (fun p => booleanPrimeShellCoefficient boundary ({p} : Finset ℕ)) ∧
      booleanDivisorTomographySum q boundary =
        q.prod (fun p => 1 + booleanPrimeShellCoefficient boundary ({p} : Finset ℕ)) := by
  constructor
  · unfold booleanPrimeShellCoefficient
    refine Finset.prod_congr rfl ?_
    intro p _hp
    simp
  · rw [booleanDivisorTomographySum_eq_localProduct]
    refine Finset.prod_congr rfl ?_
    intro p _hp
    simp [booleanPrimeShellCoefficient, add_comm]

end Omega.Conclusion
