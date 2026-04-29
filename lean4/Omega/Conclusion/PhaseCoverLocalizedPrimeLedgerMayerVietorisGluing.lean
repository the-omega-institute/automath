import Mathlib.Tactic
import Omega.Conclusion.LocalizedGroupsMayerVietoris

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-phase-cover-localized-prime-ledger-mayer-vietoris-gluing`. -/
theorem paper_conclusion_phase_cover_localized_prime_ledger_mayer_vietoris_gluing
    (S T : Finset Nat) (hSum : localizedMayerVietorisSurjective S T) :
    localizedPontryaginDualExact S T := by
  rcases paper_conclusion_localized_groups_mayer_vietoris S T hSum with
    ⟨_, _, _, hDual⟩
  exact hDual

end Omega.Conclusion
