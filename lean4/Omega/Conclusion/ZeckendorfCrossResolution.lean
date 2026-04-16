import Omega.Folding.BoundaryLayer
import Omega.Folding.ZeckendorfSignature

open Omega X

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing cross-resolution identities obtained by combining the verified `15F_n` / `16F_n`
Zeckendorf seeds with `|X_m| = F_{m+2}` and `|X_m^{bdry}| = F_{m-2}` in the audited range
`m = 10, 11, 12`.
    cor:conclusion-zeckendorf-15-16-cross-resolution -/
theorem paper_conclusion_zeckendorf_15_16_cross_resolution :
    (15 * cBoundaryCount 10 =
      Fintype.card (X 11) + Fintype.card (X 8) + Fintype.card (X 6) + Fintype.card (X 3) +
        Fintype.card (X 0)) ∧
    (16 * cBoundaryCount 10 =
      Fintype.card (X 11) + Fintype.card (X 9) + Fintype.card (X 5) + Fintype.card (X 0)) ∧
    (15 * cBoundaryCount 11 =
      Fintype.card (X 12) + Fintype.card (X 9) + Fintype.card (X 7) + Fintype.card (X 4) +
        Fintype.card (X 1)) ∧
    (16 * cBoundaryCount 11 =
      Fintype.card (X 12) + Fintype.card (X 10) + Fintype.card (X 6) + Fintype.card (X 1)) ∧
    (15 * cBoundaryCount 12 =
      Fintype.card (X 13) + Fintype.card (X 10) + Fintype.card (X 8) + Fintype.card (X 5) +
        Fintype.card (X 2)) ∧
    (16 * cBoundaryCount 12 =
      Fintype.card (X 13) + Fintype.card (X 11) + Fintype.card (X 7) + Fintype.card (X 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cBoundaryCount_eq_fib_general 10 (by omega), X.card_eq_fib 11, X.card_eq_fib 8,
      X.card_eq_fib 6, X.card_eq_fib 3, X.card_eq_fib 0]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.1
  · rw [cBoundaryCount_eq_fib_general 10 (by omega), X.card_eq_fib 11, X.card_eq_fib 9,
      X.card_eq_fib 5, X.card_eq_fib 0]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.1
  · rw [cBoundaryCount_eq_fib_general 11 (by omega), X.card_eq_fib 12, X.card_eq_fib 9,
      X.card_eq_fib 7, X.card_eq_fib 4, X.card_eq_fib 1]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.2.1
  · rw [cBoundaryCount_eq_fib_general 11 (by omega), X.card_eq_fib 12, X.card_eq_fib 10,
      X.card_eq_fib 6, X.card_eq_fib 1]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.2.1
  · rw [cBoundaryCount_eq_fib_general 12 (by omega), X.card_eq_fib 13, X.card_eq_fib 10,
      X.card_eq_fib 8, X.card_eq_fib 5, X.card_eq_fib 2]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.2.2
  · rw [cBoundaryCount_eq_fib_general 12 (by omega), X.card_eq_fib 13, X.card_eq_fib 11,
      X.card_eq_fib 7, X.card_eq_fib 2]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.2.2

end Omega.Conclusion
