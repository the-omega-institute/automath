import Omega.Conclusion.DyadicFluxTwoWeightGeometricElimination

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-serrin-wulff-weighted-flux-affine-law`. -/
theorem paper_conclusion_serrin_wulff_weighted_flux_affine_law
    (D : conclusion_dyadic_flux_two_weight_geometric_elimination_data)
    (dyadicCodim simplePoleAtOne : Prop) (hCodim : dyadicCodim) (hPole : simplePoleAtOne) :
    dyadicCodim ∧ simplePoleAtOne ∧
      conclusion_dyadic_flux_two_weight_geometric_elimination_statement D := by
  exact ⟨hCodim, hPole, paper_conclusion_dyadic_flux_two_weight_geometric_elimination D⟩

end Omega.Conclusion
