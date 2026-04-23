import Omega.SPG.DyadicTopInversionBound
import Omega.SPG.StokesGodelAlgorithmicHolographicCompleteness

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-algorithmic-sufficiency-metric-instability-separation`. -/
theorem paper_conclusion_godel_algorithmic_sufficiency_metric_instability_separation
    (D : Omega.SPG.StokesGodelAlgorithmicHolographicCompletenessData) :
    (D.complexityPreserved ∧ D.bulkRecoverableFromCode ∧ D.volumeComputableFromCode) ∧
      Omega.SPG.spg_dyadic_top_dimensional_holographic_inversion_exponential_ill_conditioning_statement := by
  exact ⟨Omega.SPG.paper_spg_stokes_godel_algorithmic_holographic_completeness D,
    Omega.SPG.paper_spg_dyadic_top_dimensional_holographic_inversion_exponential_ill_conditioning⟩

end Omega.Conclusion
