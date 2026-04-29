import Omega.Conclusion.DyadicBoundaryPrimeshellBooleanDivisorTomography

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-dyadic-boundary-primeshell-single-double-area-formulas`. -/
theorem paper_conclusion_dyadic_boundary_primeshell_single_double_area_formulas
    (f g : ℕ) (boundary : Finset ℕ) :
    booleanDivisorTomographySum ({f} : Finset ℕ) boundary =
        (if orientedBoundarySupportIncludes ({f} : Finset ℕ) boundary then
          (squarefreePrimeShellCode ({f} : Finset ℕ) : ℤ)
        else 0) ∧
      booleanDivisorTomographySum ({f, g} : Finset ℕ) boundary =
        (if orientedBoundarySupportIncludes ({f, g} : Finset ℕ) boundary then
          (squarefreePrimeShellCode ({f, g} : Finset ℕ) : ℤ)
        else 0) := by
  constructor
  · exact paper_conclusion_dyadic_boundary_primeshell_boolean_divisor_tomography
      ({f} : Finset ℕ) boundary
  · exact paper_conclusion_dyadic_boundary_primeshell_boolean_divisor_tomography
      ({f, g} : Finset ℕ) boundary

end Omega.Conclusion
