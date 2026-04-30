import Omega.Folding.FoldGaugeAnomalyP9DiscriminantSquareFiniteness

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-second-trigonal-square-discriminant-only-finite-exceptional-layer`. -/
theorem paper_conclusion_second_trigonal_square_discriminant_only_finite_exceptional_layer
    (D : Omega.Folding.fold_gauge_anomaly_p9_discriminant_square_finiteness_data) :
    Set.Finite {t : ℚ |
      t ∈
          (↑Omega.Folding.fold_gauge_anomaly_p9_discriminant_square_finiteness_audited_parameters :
            Set ℚ) ∧
        IsSquare (Omega.Folding.fold_gauge_anomaly_p9_discriminant_square_finiteness_curve t)} := by
  exact (Omega.Folding.paper_fold_gauge_anomaly_p9_discriminant_square_finiteness D).2.2.2.2.2.2

end Omega.Conclusion
