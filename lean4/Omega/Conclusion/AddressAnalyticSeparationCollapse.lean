import Omega.Conclusion.InverseLimitAddressFinitePrefixDeterminacy
import Omega.Conclusion.JoukowskyHolomorphicBlindnessRadialIdentifiability

namespace Omega.Conclusion

open Omega

noncomputable section

/-- Observable obtained by reading a finite address prefix after checking a holomorphic-moment
equality at the analytic scale parameter. -/
def conclusion_address_analytic_separation_collapse_observable (b n : ℕ)
    (a : X.XInfinity) (r : ℝ) : Option (X b) :=
  if Omega.GU.holomorphicMoment (r : ℂ) n = Omega.GU.holomorphicMoment (1 : ℂ) n then
    some (X.prefixWord a b)
  else
    none

/-- Paper label: `cor:conclusion-address-analytic-separation-collapse`.
Holomorphic blindness makes the analytic-scale slice constant, so the remaining observable is
exactly the finite-prefix address map and therefore factors through that finite prefix. -/
theorem paper_conclusion_address_analytic_separation_collapse (b n : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (∀ a : X.XInfinity,
      conclusion_address_analytic_separation_collapse_observable b n a r =
        some (X.prefixWord a b)) ∧
      ∃ m, factorsThroughPrefix (fun a : X.XInfinity => some (X.prefixWord a b)) m := by
  have hblind :
      Omega.GU.RadialQuadraticIdentifiability.holomorphicMomentBlindness r :=
    (paper_conclusion_joukowsky_holomorphic_blindness_radial_identifiability r hr).1
  refine ⟨?_, ?_⟩
  · intro a
    unfold conclusion_address_analytic_separation_collapse_observable
    simp [hblind n]
  · simpa using
      paper_conclusion_inverse_limit_address_finite_prefix_determinacy b
        (fun x : X b => some x)

end

end Omega.Conclusion
