import Omega.POM.MultiplicityCompositionMod3ZeroOneDefectSharp

namespace Omega.POM

open MultiplicityCompositionMod3ZeroOneDefectSharpData

/-- Paper label: `thm:pom-multiplicity-composition-chi-anomaly-sharp-rate`. -/
theorem paper_pom_multiplicity_composition_chi_anomaly_sharp_rate
    (Dc Di : MultiplicityCompositionMod3ZeroOneDefectSharpData) :
    SharpAsymptotic Dc.probOne Dc.oneMainTerm ∧ SharpAsymptotic Di.probOne Di.oneMainTerm := by
  exact ⟨(paper_pom_multiplicity_composition_mod3_zero_one_defect_sharp Dc).2.1,
    (paper_pom_multiplicity_composition_mod3_zero_one_defect_sharp Di).2.1⟩

end Omega.POM
