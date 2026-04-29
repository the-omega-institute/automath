import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidEndomorphismRing
import Omega.Zeta.LocalizedUnitAutomorphismGroupClassification

namespace Omega.Zeta

/-- Paper-facing package for the localized dual endomorphism-ring exhaustion. The local model
records: every endomorphism is multiplication by the image of `1`, such endomorphisms are
determined by that image, supported localized scalars act on `G_S`, unit coordinates realize the
signed localized prime monomials, and the dual endomorphism scalar ring is commutative. -/
def xi_time_part69c_localized_dual_endomorphism_ring_exhaustion_statement
    (S : FinitePrimeLocalization) : Prop :=
  LocalizedIntegersEndomorphismAutomorphismExplicit S ∧
    localizedEndomorphismScalarDescription S ∧
    localizedCrossHomDeterminedByOne S S ∧
    LocalizedUnitAutomorphismGroupClassification S ∧
    localizedSolenoidScalarRingCommutes S

/-- Paper label: `thm:xi-time-part69c-localized-dual-endomorphism-ring-exhaustion`. -/
theorem paper_xi_time_part69c_localized_dual_endomorphism_ring_exhaustion
    (S : FinitePrimeLocalization) :
    xi_time_part69c_localized_dual_endomorphism_ring_exhaustion_statement S := by
  rcases paper_xi_time_part69d_localized_solenoid_endomorphism_ring S with
    ⟨hExplicit, hEnd, _hAut, hComm⟩
  rcases paper_xi_time_part69d_localized_hom_aut_complete_classification S S with
    ⟨_hCross, hDetermined, _hAllScalar, _hEndAgain, _hAutAgain⟩
  exact ⟨hExplicit, hEnd, hDetermined,
    paper_xi_time_part69_localized_unit_automorphism_group_classification S, hComm⟩

end Omega.Zeta
