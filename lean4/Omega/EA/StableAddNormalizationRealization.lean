import Omega.EA.StableAddComputable

namespace Omega.EA.StableAddNormalizationRealization

open Omega

/-- `X.stableAdd c d` is the unique stable normal form realizing the modular sum of
stable values.
    thm:stable-add-normalization-realization -/
theorem paper_stable_add_normalization_realization (m : ℕ) (c d : X m) :
    ∃! e : X m, stableValue e = (stableValue c + stableValue d) % Nat.fib (m + 2) := by
  refine ⟨X.stableAdd c d, X.stableValue_stableAdd c d, ?_⟩
  intro e he
  apply X.eq_of_stableValue_eq
  rw [he, X.stableValue_stableAdd]

end Omega.EA.StableAddNormalizationRealization
