import Mathlib.Tactic
import Omega.Zeta.LocalizedHomAutCompleteClassification
import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit

namespace Omega.Zeta

/-- The concrete scalar model used for the localized-solenoid endomorphism ring. -/
abbrev LocalizedSolenoidScalarRing (S : FinitePrimeLocalization) :=
  SupportedLocalizedIntegerGroup S

/-- The scalar model is commutative because it sits inside `ℚ`. -/
def localizedSolenoidScalarRingCommutes (S : FinitePrimeLocalization) : Prop :=
  ∀ u v : LocalizedSolenoidScalarRing S, u.1 * v.1 = v.1 * u.1

/-- Continuous localized-solenoid endomorphisms are identified with the same localization ring as
on the discrete side, automorphisms are the unit scalars, and the opposite-ring issue disappears
because multiplication of localized rationals is commutative. -/
def LocalizedSolenoidEndomorphismRing (S : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  LocalizedIntegersEndomorphismAutomorphismExplicit S ∧
    localizedEndomorphismScalarDescription S ∧
    localizedAutomorphismUnitDescription S ∧
    localizedSolenoidScalarRingCommutes S

/-- Paper label: `thm:xi-time-part69d-localized-solenoid-endomorphism-ring`. -/
theorem paper_xi_time_part69d_localized_solenoid_endomorphism_ring
    (S : Omega.Zeta.FinitePrimeLocalization) : LocalizedSolenoidEndomorphismRing S := by
  have hExplicit := paper_xi_localized_integers_endomorphism_automorphism_explicit S
  rcases paper_xi_time_part69d_localized_hom_aut_complete_classification S S with
    ⟨_, _, _, hEnd, hAut⟩
  refine ⟨hExplicit, hEnd, hAut, ?_⟩
  intro u v
  exact mul_comm u.1 v.1

end Omega.Zeta
