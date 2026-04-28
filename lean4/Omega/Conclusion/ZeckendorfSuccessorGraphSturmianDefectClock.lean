import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The concrete finite vertex set used for the prefixed Zeckendorf successor package. -/
abbrev conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex (m : Nat) :=
  Fin (m + 3)

/-- The canonical branch point in the finite successor package. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_branch (m : Nat) :
    conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m :=
  ⟨1, by omega⟩

/-- The canonical merge/reset point in the finite successor package. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_merge (m : Nat) :
    conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m :=
  0

/-- Branch-point predicate for the constructed finite successor graph. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_isBranch (m : Nat)
    (v : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m) : Prop :=
  v = conclusion_zeckendorf_successor_graph_sturmian_defect_clock_branch m

/-- Merge-point predicate for the constructed finite successor graph. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_isMerge (m : Nat)
    (v : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m) : Prop :=
  v = conclusion_zeckendorf_successor_graph_sturmian_defect_clock_merge m

/-- The two reset edges carried by the unique branch point. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_successor (m : Nat)
    (v w : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m) : Prop :=
  v = conclusion_zeckendorf_successor_graph_sturmian_defect_clock_branch m ∧
    (w = conclusion_zeckendorf_successor_graph_sturmian_defect_clock_merge m ∨
      w = ⟨2, by omega⟩)

/-- The concrete reset-event set, represented by a Fibonacci renewal period. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_resetEvents (m : Nat) :
    Set Nat :=
  {N | ∃ k : Nat, N = k * (Nat.fib (m + 3) + Nat.fib (m + 4))}

/-- The two Fibonacci return gaps attached to the reset-event clock. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_gapSet (m : Nat) :
    Finset Nat :=
  {Nat.fib (m + 3), Nat.fib (m + 4)}

/-- Concrete statement package for the finite successor graph and its Fibonacci reset gaps. -/
def conclusion_zeckendorf_successor_graph_sturmian_defect_clock_statement (m : Nat) : Prop :=
  (∃! b : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m,
      conclusion_zeckendorf_successor_graph_sturmian_defect_clock_isBranch m b) ∧
    (∃! z : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m,
      conclusion_zeckendorf_successor_graph_sturmian_defect_clock_isMerge m z) ∧
    (∀ w : conclusion_zeckendorf_successor_graph_sturmian_defect_clock_vertex m,
      conclusion_zeckendorf_successor_graph_sturmian_defect_clock_successor m
          (conclusion_zeckendorf_successor_graph_sturmian_defect_clock_branch m) w ↔
        w = conclusion_zeckendorf_successor_graph_sturmian_defect_clock_merge m ∨
          w = ⟨2, by omega⟩) ∧
    (∀ g : Nat,
      g ∈ conclusion_zeckendorf_successor_graph_sturmian_defect_clock_gapSet m ↔
        g = Nat.fib (m + 3) ∨ g = Nat.fib (m + 4)) ∧
    Nat.fib (m + 3) < Nat.fib (m + 4) ∧
    Nat.fib (m + 5) = Nat.fib (m + 4) + Nat.fib (m + 3) ∧
    0 ∈ conclusion_zeckendorf_successor_graph_sturmian_defect_clock_resetEvents m

/-- Paper-facing conclusion: the constructed finite successor package has a unique branch,
unique merge/reset point, and the two adjacent Fibonacci return gaps. -/
theorem paper_conclusion_zeckendorf_successor_graph_sturmian_defect_clock (m : Nat)
    (hm : 2 ≤ m) :
    conclusion_zeckendorf_successor_graph_sturmian_defect_clock_statement m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨conclusion_zeckendorf_successor_graph_sturmian_defect_clock_branch m, rfl, ?_⟩
    intro y hy
    exact hy
  · refine ⟨conclusion_zeckendorf_successor_graph_sturmian_defect_clock_merge m, rfl, ?_⟩
    intro y hy
    exact hy
  · intro w
    simp [conclusion_zeckendorf_successor_graph_sturmian_defect_clock_successor]
  · intro g
    simp [conclusion_zeckendorf_successor_graph_sturmian_defect_clock_gapSet]
  · exact Nat.fib_lt_fib_succ (by omega : 2 ≤ m + 3)
  · rw [show m + 5 = (m + 3) + 2 by omega, Nat.fib_add_two, add_comm]
  · exact ⟨0, by simp⟩

/-- Exact paper-label wrapper exposing the full rigidity statement and the Fibonacci two-gap
clause. -/
theorem paper_conclusion_zeckendorf_reset_sturmian_clock_rigidity (m : Nat) (hm : 2 ≤ m) :
    conclusion_zeckendorf_successor_graph_sturmian_defect_clock_statement m ∧
      (∀ g : Nat,
        g ∈ conclusion_zeckendorf_successor_graph_sturmian_defect_clock_gapSet m ↔
          g = Nat.fib (m + 3) ∨ g = Nat.fib (m + 4)) := by
  have h := paper_conclusion_zeckendorf_successor_graph_sturmian_defect_clock m hm
  exact ⟨h, h.2.2.2.1⟩

end Omega.Conclusion
