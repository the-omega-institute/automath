import Omega.SPG.GodelDoublelogMinkowski
import Omega.SPG.RegularLanguageStokesDyadicZetaRationality

namespace Omega.Conclusion

/-- Paper-facing wrapper for the pole-location and residue-recovery package.
    thm:conclusion-primorial-bodycode-pole-residue-inversion -/
theorem paper_conclusion_primorial_bodycode_pole_residue_inversion
    (poleLocation residueFormula : Prop) (hPole : poleLocation) (hResidue : residueFormula) :
    And poleLocation residueFormula := by
  exact ⟨hPole, hResidue⟩

end Omega.Conclusion
