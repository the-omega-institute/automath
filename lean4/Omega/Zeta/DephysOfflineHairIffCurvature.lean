import Mathlib.Tactic

namespace Omega.Zeta

/-- The no-hair and curvature-reduction interfaces package the offline-hair equivalence,
strictification equivalence, and the finite-search and epsilon-sound certificate flags.
    cor:dephys-offline-hair-iff-curvature -/
theorem paper_dephys_offline_hair_iff_curvature
    (offlineHair nonzeroAnom noHair universalStrictification finiteSearch epsSound : Prop)
    (hoffline : offlineHair ↔ nonzeroAnom)
    (hnohair : noHair ↔ universalStrictification)
    (hcert : finiteSearch ∧ epsSound) :
    (offlineHair ↔ nonzeroAnom) ∧
      (noHair ↔ universalStrictification) ∧ finiteSearch ∧ epsSound := by
  exact ⟨hoffline, hnohair, hcert⟩

end Omega.Zeta
