import Omega.Folding.MomentSum

namespace Omega.Conclusion

/-- Connected gauge-group dimension in the binary collision model. -/
noncomputable def conclusion_collision2_lie_dim_rank_aut_dim (m : Nat) : Nat :=
  Omega.momentSum 2 m - Nat.fib (m + 2)

/-- Connected gauge-group rank in the binary collision model. -/
def conclusion_collision2_lie_dim_rank_aut_rank (m : Nat) : Nat :=
  2 ^ m - Nat.fib (m + 2)

/-- Paper label: `cor:conclusion-collision2-lie-dim-rank`. -/
theorem paper_conclusion_collision2_lie_dim_rank (m : Nat) :
    conclusion_collision2_lie_dim_rank_aut_dim m = Omega.momentSum 2 m - Nat.fib (m + 2) ∧
      conclusion_collision2_lie_dim_rank_aut_rank m = 2 ^ m - Nat.fib (m + 2) := by
  simp [conclusion_collision2_lie_dim_rank_aut_dim,
    conclusion_collision2_lie_dim_rank_aut_rank]

end Omega.Conclusion
