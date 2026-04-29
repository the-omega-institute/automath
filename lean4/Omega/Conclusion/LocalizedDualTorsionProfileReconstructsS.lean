import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-localized-dual-torsion-profile-reconstructs-S`. -/
theorem paper_conclusion_localized_dual_torsion_profile_reconstructs_s
    (isPrime : Nat → Prop) [DecidablePred isPrime] (S T : Finset Nat)
    (kernelCard : Nat → Nat)
    (hS : ∀ p, p ∈ S ↔ isPrime p ∧ kernelCard p = 1)
    (hT : ∀ p, p ∈ T ↔ isPrime p ∧ kernelCard p = 1) :
    S = T := by
  ext p
  exact (hS p).trans (hT p).symm

end Omega.Conclusion
