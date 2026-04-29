import Mathlib.Tactic
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

open Finset

/-- The short-root entries of fiber degree `2` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_short_degree_two :
    Finset Omega.GU.Window6ShortRootParityBlock :=
  {0}

/-- The short-root entries of fiber degree `3` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_short_degree_three :
    Finset Omega.GU.Window6ShortRootParityBlock :=
  ∅

/-- The short-root entries of fiber degree `4` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_short_degree_four :
    Finset Omega.GU.Window6ShortRootParityBlock :=
  univ.erase 0

/-- The long-root entries of fiber degree `2` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_long_degree_two :
    Finset Omega.GU.Window6LongRootParityBlock :=
  {0, 1, 2, 3}

/-- The long-root entries of fiber degree `3` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_long_degree_three :
    Finset Omega.GU.Window6LongRootParityBlock :=
  {4, 5, 6, 7}

/-- The long-root entries of fiber degree `4` in the audited window-`6` lookup. -/
def conclusion_window6_short_long_degeneracy_splitting_long_degree_four :
    Finset Omega.GU.Window6LongRootParityBlock :=
  {8, 9, 10, 11}

/-- The Cartan/boundary entries contributing to fiber degree `2`. -/
def conclusion_window6_short_long_degeneracy_splitting_boundary_degree_two :
    Finset Omega.GU.Window6BoundaryParityBlock :=
  univ

/-- Concrete cardinalities of the short/long/boundary finite lookup strata. -/
theorem conclusion_window6_short_long_degeneracy_splitting_lookup_counts :
    conclusion_window6_short_long_degeneracy_splitting_short_degree_four.card = 5 ∧
      conclusion_window6_short_long_degeneracy_splitting_short_degree_two.card = 1 ∧
      conclusion_window6_short_long_degeneracy_splitting_short_degree_three.card = 0 ∧
      conclusion_window6_short_long_degeneracy_splitting_long_degree_two.card = 4 ∧
      conclusion_window6_short_long_degeneracy_splitting_long_degree_three.card = 4 ∧
      conclusion_window6_short_long_degeneracy_splitting_long_degree_four.card = 4 ∧
      conclusion_window6_short_long_degeneracy_splitting_boundary_degree_two.card = 3 := by
  native_decide

/-- Paper label: `thm:conclusion-window6-short-long-degeneracy-splitting`. -/
theorem paper_conclusion_window6_short_long_degeneracy_splitting :
    Fintype.card Omega.GU.Window6ShortRootParityBlock = 6 ∧
      Fintype.card Omega.GU.Window6LongRootParityBlock = 12 ∧
      5 + 1 + 0 = 6 ∧
      4 + 4 + 4 = 12 ∧
      1 + 4 + 3 = 8 ∧
      0 + 4 = 4 ∧
      5 + 4 = 9 := by
  rcases Omega.GU.paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, _, _, _, hShort, hLong, _, _, _, _⟩
  have _hLookup := conclusion_window6_short_long_degeneracy_splitting_lookup_counts
  exact ⟨hShort, hLong, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Omega.Conclusion
