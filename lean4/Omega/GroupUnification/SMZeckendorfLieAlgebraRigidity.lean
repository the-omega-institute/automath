import Mathlib.Tactic
import Omega.Folding.ZeckendorfSignature

namespace Omega.GroupUnification

/-- Paper label: `prop:sm-zeckendorf-lie-algebra-rigidity`.
This is the paper-facing wrapper around the audited Fibonacci identities and the no-adjacent-gap
certificate for the standard-model Zeckendorf decomposition of `12`. -/
theorem paper_sm_zeckendorf_lie_algebra_rigidity :
    Nat.fib 6 + Nat.fib 4 + Nat.fib 2 = 12 ∧
      Nat.fib 2 = 1 ∧
      Nat.fib 4 = 3 ∧
      Nat.fib 6 = 8 ∧
      4 - 2 ≥ 2 ∧
      6 - 4 ≥ 2 := by
  rcases Omega.ZeckSig.sm_boundary_count with ⟨hSum, hFib2, hFib4, hFib6⟩
  rcases Omega.ZeckSig.sm_zeckendorf_no_adjacent with ⟨hGap24, hGap46⟩
  refine ⟨Omega.ZeckSig.sm_zeckendorf_twelve, hFib2, hFib4, hFib6, hGap24, hGap46⟩

end Omega.GroupUnification
