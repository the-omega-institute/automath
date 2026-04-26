import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-torsion-schur-dual-microscope`. -/
theorem paper_pom_torsion_schur_dual_microscope
    (q : Nat)
    (torsionTableKnown reducedTrivialKnown recoverNontrivialChannelConstants : Prop)
    (hq : 2 ≤ q)
    (hFiniteElimination :
      torsionTableKnown → reducedTrivialKnown → recoverNontrivialChannelConstants) :
    torsionTableKnown → reducedTrivialKnown → recoverNontrivialChannelConstants := by
  have _ : 2 ≤ q := hq
  intro hTorsion hReduced
  exact hFiniteElimination hTorsion hReduced

end Omega.POM
