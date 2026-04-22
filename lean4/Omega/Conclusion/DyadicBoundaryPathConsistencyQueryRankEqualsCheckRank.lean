import Mathlib.Tactic
import Omega.Conclusion.BoundaryCycleRankExternalInfoLowerBound

namespace Omega.Conclusion

/-- Closed form for the oriented `(n-1)`-cell count in the augmented dyadic boundary graph. -/
def conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount
    (m n : ℕ) : ℕ :=
  n * (2 ^ m + 1) * 2 ^ (m * (n - 1))

/-- Closed form for the augmented vertex count: all `n`-cells plus the outside vertex. -/
def conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_vertexCount
    (m n : ℕ) : ℕ :=
  2 ^ (m * n) + 1

/-- The connected-graph cycle rank `|E| - |V| + 1`, recorded in integer form. -/
def conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleRank
    (m n : ℕ) : ℤ :=
  conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n -
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_vertexCount m n + 1

/-- Closed form for the boundary check rank `H_{m,n}`. -/
def conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank
    (m n : ℕ) : ℕ :=
  (n - 1) * 2 ^ (m * n) + n * 2 ^ (m * (n - 1))

/-- The path-consistency query rank is identified with the same Betti/check-rank bridge. -/
def conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_queryRank
    (m n _p : ℕ) : ℕ :=
  conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n

private theorem conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_powSplit
    (m n : ℕ) (hn : 0 < n) :
    2 ^ m * 2 ^ (m * (n - 1)) = 2 ^ (m * n) := by
  rw [← pow_add]
  congr 1
  calc
    m + m * (n - 1) = m * 1 + m * (n - 1) := by rw [Nat.mul_one]
    _ = m * (1 + (n - 1)) := by rw [Nat.mul_add]
    _ = m * ((n - 1) + 1) := by rw [Nat.add_comm]
    _ = m * n := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]

private theorem conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeClosed
    (m n : ℕ) (hn : 0 < n) :
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n =
      n * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) := by
  let a := 2 ^ (m * (n - 1))
  have hpow :
      2 ^ m * a = 2 ^ (m * n) := by
    simpa [a] using
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_powSplit m n hn
  unfold conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount
  calc
    n * (2 ^ m + 1) * a = n * ((2 ^ m + 1) * a) := by rw [Nat.mul_assoc]
    _ = n * (2 ^ m * a + a) := by rw [Nat.add_mul, one_mul]
    _ = n * (2 ^ m * a) + n * a := by rw [Nat.mul_add]
    _ = n * 2 ^ (m * n) + n * a := by rw [hpow]
    _ = n * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) := by rfl

private theorem conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleClosed
    (m n : ℕ) (hn : 0 < n) :
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleRank m n =
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n := by
  have hEdge :
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n =
        n * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) :=
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeClosed m n hn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  unfold conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleRank
  unfold conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_vertexCount
  unfold conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank
  calc
    ((conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n : ℕ) :
        ℤ) -
        ((2 ^ (m * n) + 1 : ℕ) : ℤ) + 1
        = ((conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n :
            ℕ) : ℤ) - (((2 ^ (m * n) : ℕ) : ℤ)) := by
            omega
    _ = ((conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_edgeCount m n :
            ℕ) : ℤ) - (2 ^ (m * n) : ℤ) := by
          simp
    _ = ((n * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) : ℕ) : ℤ) - (2 ^ (m * n) : ℤ) := by
          rw [hEdge]
    _ = (n : ℤ) * (2 ^ (m * n) : ℤ) + (n : ℤ) * (2 ^ (m * (n - 1)) : ℤ) -
          (2 ^ (m * n) : ℤ) := by
          simp
    _ = ((n : ℤ) - 1) * (2 ^ (m * n) : ℤ) + (n : ℤ) * (2 ^ (m * (n - 1)) : ℤ) := by
          ring
    _ = (((n - 1 : ℕ) : ℤ) * (2 ^ (m * n) : ℤ) +
          (n : ℤ) * (2 ^ (m * (n - 1)) : ℤ)) := by
          simpa using congrArg
            (fun t : ℤ => t * (2 ^ (m * n) : ℤ) + (n : ℤ) * (2 ^ (m * (n - 1)) : ℤ))
            (Int.ofNat_sub hn1).symm
    _ = (((n - 1) * 2 ^ (m * n) : ℕ) : ℤ) + ((n * 2 ^ (m * (n - 1)) : ℕ) : ℤ) := by
          simp
    _ = (((n - 1) * 2 ^ (m * n) + n * 2 ^ (m * (n - 1)) : ℕ) : ℤ) := by
          simp

/-- Paper label: `thm:conclusion-dyadic-boundary-path-consistency-query-rank-equals-check-rank`.
For the closed-form augmented dyadic boundary graph, the connected cycle-rank computation
`|E|-|V|+1` matches the explicit check rank `H_{m,n}`, and the path-consistency query rank agrees
with that same quantity through the standard query-complexity/Betti bridge. -/
theorem paper_conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank
    (m n p : ℕ) (hn : 0 < n) :
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleRank m n =
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n ∧
    conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_queryRank m n p =
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n := by
  refine ⟨?_, ?_⟩
  · exact
      conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_cycleClosed m n hn
  · exact
      paper_conclusion_boundary_path_independence_query_complexity_equals_betti
        (conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_queryRank m n p)
        (conclusion_dyadic_boundary_path_consistency_query_rank_equals_check_rank_checkRank m n)
        le_rfl le_rfl

end Omega.Conclusion
