import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidEndomorphismRing

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-endomorphism-ring-solenoid-indecomposable`. -/
theorem paper_xi_localized_endomorphism_ring_solenoid_indecomposable
    (S : Omega.Zeta.FinitePrimeLocalization) :
    Omega.Zeta.LocalizedSolenoidEndomorphismRing S ∧
      (∀ e : Omega.Zeta.SupportedLocalizedIntegerGroup S,
        e.1 * e.1 = e.1 → e.1 = 0 ∨ e.1 = 1) := by
  refine ⟨Omega.Zeta.paper_xi_time_part69d_localized_solenoid_endomorphism_ring S, ?_⟩
  intro e he
  have hfactor : e.1 * (e.1 - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (by linarith)

end Omega.Zeta
