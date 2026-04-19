import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.BoundaryLayer
import Omega.Folding.ZeckendorfSignature

namespace Omega.GU

open Omega

/-- The `m = 11` boundary branch forced by the `δ = 34` uplift, together with the
minimal `45`-dimensional boundary sum and the Zeckendorf census isolating the
`so(10)` dimension.
    thm:m11-delta-closure-unique-minimal-so10 -/
theorem paper_m11_delta_closure_unique_minimal_so10 :
    (∀ m : Nat, 3 ≤ m → Nat.fib (m - 2) = 34 → m = 11) ∧
    ({6, 8, 11} : Finset Nat).sum cBoundaryCount = 45 ∧
    45 = Nat.fib 9 + Nat.fib 6 + Nat.fib 4 ∧
    (∀ d ∈ [3, 8, 10, 14, 15, 21, 24, 28, 35, 36],
      Nat.zeckendorf d ≠ Nat.zeckendorf 45) ∧
    (∀ d ∈ ({52, 78, 133, 248} : Finset Nat), Nat.zeckendorf d ≠ Nat.zeckendorf 45) := by
  rcases Omega.ZeckSig.nap_so10_minimality with ⟨hso10, hclassical⟩
  refine ⟨?_, ?_, hso10, hclassical, ?_⟩
  · intro m hm h
    exact Omega.ZeckSig.bdry_delta34_m11_uniqueness m hm h
  · simp [cBoundaryCount_six, cBoundaryCount_eight, cBoundaryCount_eleven]
  · native_decide

end Omega.GU
