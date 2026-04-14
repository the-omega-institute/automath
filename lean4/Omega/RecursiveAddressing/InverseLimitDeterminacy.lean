import Omega.Folding.InverseLimitTopology

namespace Omega.RecursiveAddressing.InverseLimitDeterminacy

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a compatible inverse-limit family determines a unique stable address, and
    stable addresses are exactly determined by their finite prefixes.
    thm:inverse-limit-determinacy -/
theorem paper_scan_projection_address_inverse_limit_determinacy_seeds :
    (∀ F : Omega.X.CompatibleFamily, ∃! a : Omega.X.XInfinity, Omega.X.toFamily a = F) ∧
    (∀ a b : Omega.X.XInfinity, (∀ m, Omega.X.prefixWord a m = Omega.X.prefixWord b m) ↔ a = b) ∧
    Function.Bijective (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) := by
  refine ⟨?_, ?_, Omega.X.CompatibleFamily_complete⟩
  · intro F
    refine ⟨Omega.X.ofFamily F, Omega.X.toFamily_ofFamily F, ?_⟩
    intro a ha
    have := congrArg Omega.X.ofFamily ha
    simpa using this
  · intro a b
    exact (Omega.X.XInfinity_eq_iff a b).symm

/-- Wrapper theorem matching the ETDS publication label.
    thm:inverse-limit-determinacy -/
theorem paper_scan_projection_address_inverse_limit_determinacy_package :
    (∀ F : Omega.X.CompatibleFamily, ∃! a : Omega.X.XInfinity, Omega.X.toFamily a = F) ∧
    (∀ a b : Omega.X.XInfinity, (∀ m, Omega.X.prefixWord a m = Omega.X.prefixWord b m) ↔ a = b) ∧
    Function.Bijective (Omega.X.ofFamily : Omega.X.CompatibleFamily → Omega.X.XInfinity) :=
  paper_scan_projection_address_inverse_limit_determinacy_seeds

end Omega.RecursiveAddressing.InverseLimitDeterminacy
