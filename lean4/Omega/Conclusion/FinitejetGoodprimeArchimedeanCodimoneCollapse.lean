import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finitejet-goodprime-archimedean-codimone-collapse`. -/
theorem paper_conclusion_finitejet_goodprime_archimedean_codimone_collapse
    (finiteJetDeterminesData pAdicGoodPrimeUniqueness archimedeanSingularValueBounds
      codimOneCollapse : Prop)
    (hJet : finiteJetDeterminesData) (hPadic : pAdicGoodPrimeUniqueness)
    (hArch : archimedeanSingularValueBounds) (hCollapse : codimOneCollapse) :
    finiteJetDeterminesData ∧ pAdicGoodPrimeUniqueness ∧ archimedeanSingularValueBounds ∧
      codimOneCollapse := by
  exact ⟨hJet, hPadic, hArch, hCollapse⟩

end Omega.Conclusion
