import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.PhaseChannelCrowdingLowerBound

namespace Omega.Conclusion

/-- The squarefree prime-ledger family on the first `m` primes is modeled by a Boolean cube with
`2^m` vertices. -/
def conclusion_squarefree_crowding_kphase_boolean_cube_cardinality (m : ℕ) : ℕ :=
  2 ^ m

/-- Partitioning the `k`-torus fundamental domain into `Q` intervals on each axis yields `Q^k`
cells. -/
def conclusion_squarefree_crowding_kphase_cell_count (Q k : ℕ) : ℕ :=
  Q ^ k

/-- Paper label: `thm:conclusion-squarefree-crowding-kphase`. Once the `2^m` squarefree ledgers are
sent into only `Q^k` torus cells with `Q^k < 2^m`, the pigeonhole principle produces two distinct
ledger states in the same cell. -/
theorem paper_conclusion_squarefree_crowding_kphase
    (m Q k : ℕ)
    (hQ : conclusion_squarefree_crowding_kphase_cell_count Q k <
      conclusion_squarefree_crowding_kphase_boolean_cube_cardinality m)
    (cellOf :
      Fin (conclusion_squarefree_crowding_kphase_boolean_cube_cardinality m) →
        Fin (conclusion_squarefree_crowding_kphase_cell_count Q k)) :
    ∃ u v :
        Fin (conclusion_squarefree_crowding_kphase_boolean_cube_cardinality m),
      u ≠ v ∧ cellOf u = cellOf v := by
  let D : PhaseChannelCrowdingData :=
    { boxPointCount := conclusion_squarefree_crowding_kphase_boolean_cube_cardinality m
      cellCount := conclusion_squarefree_crowding_kphase_cell_count Q k
      cellOf := cellOf
      crowded := hQ }
  rcases paper_conclusion_phase_channel_crowding_lb D with ⟨n, hn, -, hcell⟩
  refine ⟨n.1.1, n.1.2, hn, hcell⟩

end Omega.Conclusion
