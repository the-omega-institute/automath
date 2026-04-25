import Omega.POM.IndMatrixGrammar

namespace Omega.POM

/-- Paper label: `lem:pom-ind-local-recurrence`.
On a single radius-`2` block, the three-point window only has the two local predecessor branches
from the paper: if the left endpoint is already compatible with the right endpoint then
`p(t) = t - 2`, while the dense triple `k = i + 2` forces the defect branch `p(t) = t - 3`.
The audited DP recurrence is exactly the one from `paper_pom_independence_dp_radius2`. -/
theorem paper_pom_ind_local_recurrence
    (i j k a b c : ℕ)
    (hij : i < j) (hjk : j < k)
    (hblock₁ : j ≤ i + 2) (hblock₂ : k ≤ j + 2) :
    (i + 2 < k →
        predecessorIndexRadius2 k [i, j, k] = 1 ∧
          pomTripleStep 2 (a, b, c) = (a + b, a, b)) ∧
      (k = i + 2 →
        predecessorIndexRadius2 k [i, j, k] = 0 ∧
          pomTripleStep 3 (a, b, c) = (a + c, a, b)) ∧
      indepCountRadius2 [i, j, k] = dpCountRadius2 [i, j, k] := by
  refine ⟨?_, ?_, ?_⟩
  · intro hik
    refine ⟨?_, rfl⟩
    unfold predecessorIndexRadius2 predecessorPrefixRadius2
    have hnotjk : ¬ j + 2 < k := by
      omega
    simp [if_pos hik, predecessorPrefixRadius2, if_neg hnotjk]
  · intro hik
    refine ⟨?_, rfl⟩
    unfold predecessorIndexRadius2 predecessorPrefixRadius2
    have hnotik : ¬ i + 2 < k := by
      omega
    have hnotjk : ¬ j + 2 < k := by
      omega
    simp [if_neg hnotik, predecessorPrefixRadius2, if_neg hnotjk]
  · simpa [List.pairwise_cons, hij, hjk, Nat.lt_trans hij hjk] using
      paper_pom_independence_dp_radius2 [i, j, k]
        (by simp [List.pairwise_cons, hij, hjk, Nat.lt_trans hij hjk])

end Omega.POM
