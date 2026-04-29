import Omega.EA.Wedderburn

namespace Omega.EA

/-- Concrete Wedderburn bookkeeping package for the fold groupoid algebra at stage `m`.
    `prop:fold-groupoid-wedderburn` -/
def fold_groupoid_wedderburn_statement (m : Nat) : Prop :=
  (∑ x : X m, (X.fiberMultiplicity x) ^ 2 = momentSum 2 m) ∧
    (∑ x : X m, (X.fiberMultiplicity x) ^ 3 = momentSum 3 m) ∧
    (∑ x : X m, (X.fiberMultiplicity x) ^ 4 = momentSum 4 m) ∧
    (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) ∧
    momentSum 0 m = Nat.fib (m + 2) ∧
    (m = 6 →
      cFiberHist 6 1 = 2 ∧
        cFiberHist 6 2 = 4 ∧
        cFiberHist 6 3 = 8 ∧
        cFiberHist 6 4 = 5 ∧
        cFiberHist 6 5 = 2 ∧
        momentSum 2 6 = 220 ∧
        momentSum 3 6 = 820 ∧
        momentSum 4 6 = 3244)

/-- Paper-facing Wedderburn decomposition and bookkeeping package.
    `prop:fold-groupoid-wedderburn` -/
theorem paper_fold_groupoid_wedderburn (m : Nat) : fold_groupoid_wedderburn_statement m := by
  refine ⟨wedderburn_total_dim_eq_S2 m, (paper_pom_fiber_index_cgf_q3_specialized m).1,
    (paper_pom_fiber_index_cgf_q4_specialized m).1, X.fiberMultiplicity_total m,
    momentSum_zero m, ?_⟩
  intro hm
  subst hm
  rcases fiber_histogram_m6 with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3, h4, h5, momentSum_two_six, momentSum_three_six, momentSum_four_six⟩

end Omega.EA
