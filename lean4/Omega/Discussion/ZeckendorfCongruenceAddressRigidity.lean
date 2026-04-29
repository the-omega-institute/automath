import Omega.Folding.FiberArithmeticProperties

namespace Omega.Discussion

/-- The Zeckendorf congruence condition already pins down the folded address uniquely.
    prop:discussion-zeckendorf-congruence-address-rigidity -/
theorem paper_discussion_zeckendorf_congruence_address_rigidity (m : ℕ)
    (Φ : Omega.Word m → Omega.X m)
    (hΦ : ∀ ω : Omega.Word m,
      Omega.stableValue (Φ ω) = Omega.weight ω % Nat.fib (m + 2)) :
    ∀ ω : Omega.Word m, Φ ω = Omega.Fold ω := by
  simpa using Omega.Fold_unique_of_stableValue_mod (m := m) Φ hΦ

end Omega.Discussion
