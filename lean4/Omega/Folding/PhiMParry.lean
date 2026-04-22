import Omega.Folding.GmFischerCover

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the `Φ_m` Parry package: irreducibility and Perron-Frobenius
data give the Parry measure, and the cylinder formula follows from that measure.
    prop:Phi_m-parry -/
theorem paper_phi_m_parry_measure
    (m : Nat) (coverIrreducible pfEigenData parryMeasure cylinderFormula : Prop)
    (hParry : coverIrreducible -> pfEigenData -> parryMeasure)
    (hCyl : parryMeasure -> cylinderFormula) :
    coverIrreducible -> pfEigenData -> parryMeasure ∧ cylinderFormula := by
  let _ := m
  intro hCover hPf
  have hParryMeasure : parryMeasure := hParry hCover hPf
  exact ⟨hParryMeasure, hCyl hParryMeasure⟩

end Omega.Folding
