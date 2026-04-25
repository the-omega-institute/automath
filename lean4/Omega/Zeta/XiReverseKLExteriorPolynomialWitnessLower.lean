theorem paper_xi_reversekl_exterior_polynomial_witness_lower
    (fenchelPoissonDuality jensenExteriorWitness fourierCoefficientExpansion explicitLowerBound :
      Prop)
    (hDual : fenchelPoissonDuality)
    (hJensen : jensenExteriorWitness)
    (hFourier : fourierCoefficientExpansion)
    (hLower :
      fenchelPoissonDuality →
        jensenExteriorWitness →
          fourierCoefficientExpansion →
            explicitLowerBound) :
    fenchelPoissonDuality ∧
      jensenExteriorWitness ∧
        fourierCoefficientExpansion ∧
          explicitLowerBound := by
  exact ⟨hDual, hJensen, hFourier, hLower hDual hJensen hFourier⟩
