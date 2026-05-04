import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-dynamical-centralizer-torus-collapse`. -/
theorem paper_conclusion_window6_dynamical_centralizer_torus_collapse
    (H : Type*) (commutesWithT6 conjugatesIntoTorus abelianLie noNonabelianGeometry : Prop)
    (hToral : commutesWithT6 → conjugatesIntoTorus)
    (hAbelian : conjugatesIntoTorus → abelianLie)
    (hNoGeom : abelianLie → noNonabelianGeometry) (hcomm : commutesWithT6) :
    conjugatesIntoTorus ∧ abelianLie ∧ noNonabelianGeometry := by
  let _centralizerType := H
  have hTorus : conjugatesIntoTorus := hToral hcomm
  have hLie : abelianLie := hAbelian hTorus
  exact ⟨hTorus, hLie, hNoGeom hLie⟩

end Omega.Conclusion
