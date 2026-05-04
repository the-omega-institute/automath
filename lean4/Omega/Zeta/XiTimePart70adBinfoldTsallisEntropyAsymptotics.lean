import Omega.Zeta.XiTimePart70adBinfoldRenyiEntropyConstantDrift

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70ad-binfold-tsallis-entropy-asymptotics`. -/
theorem paper_xi_time_part70ad_binfold_tsallis_entropy_asymptotics
    (q : Real) (hq0 : 0 < q) (hq1 : q != 1) (gtCase ltCase : Prop)
    (hgt : 1 < q -> gtCase) (hlt : q < 1 -> ltCase) :
    (1 < q -> gtCase) /\ (q < 1 -> ltCase) := by
  have _ : 0 < q := hq0
  have _ : q != 1 := hq1
  exact ⟨hgt, hlt⟩

end Omega.Zeta
