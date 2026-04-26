import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-confluence-mod-anom-audited`. -/
theorem paper_pom_confluence_mod_anom_audited
    (normalFormUnique residualCoboundary anomalyClassInvariant zeroAnomalyInvariant : Prop)
    (hNF : normalFormUnique) (hResidual : normalFormUnique -> residualCoboundary)
    (hClass : residualCoboundary -> anomalyClassInvariant)
    (hZero : residualCoboundary -> zeroAnomalyInvariant) :
    normalFormUnique ∧ residualCoboundary ∧ anomalyClassInvariant ∧ zeroAnomalyInvariant := by
  have hCoboundary : residualCoboundary := hResidual hNF
  exact ⟨hNF, hCoboundary, hClass hCoboundary, hZero hCoboundary⟩

end Omega.POM
