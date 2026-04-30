import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalGenus

namespace Omega.Conclusion

/-- The two trigonal structures carried by the conclusion-level host. -/
inductive conclusion_cf_two_trigonal_structures_never_equivalent_structure
  | first
  | second
  deriving DecidableEq, Repr

/-- The branch-index profile attached to each trigonal cover. -/
def conclusion_cf_two_trigonal_structures_never_equivalent_branch_profile :
    conclusion_cf_two_trigonal_structures_never_equivalent_structure → List ℕ
  | .first => [3, 3, 2, 2, 2, 2, 2, 2]
  | .second => List.replicate 10 2

/-- The genus of the `S₃` Galois closure attached to each trigonal cover. -/
def conclusion_cf_two_trigonal_structures_never_equivalent_closure_genus :
    conclusion_cf_two_trigonal_structures_never_equivalent_structure → ℕ
  | .first => 8
  | .second => 10

/-- Equivalence of trigonal covers preserves the branch profile and the Galois-closure genus. -/
def conclusion_cf_two_trigonal_structures_never_equivalent_cover_equivalent
    (a b : conclusion_cf_two_trigonal_structures_never_equivalent_structure) : Prop :=
  conclusion_cf_two_trigonal_structures_never_equivalent_branch_profile a =
      conclusion_cf_two_trigonal_structures_never_equivalent_branch_profile b ∧
    conclusion_cf_two_trigonal_structures_never_equivalent_closure_genus a =
      conclusion_cf_two_trigonal_structures_never_equivalent_closure_genus b

/-- Concrete statement package for the invariant obstruction to equivalence of the two trigonal
structures. -/
def conclusion_cf_two_trigonal_structures_never_equivalent_statement : Prop :=
  conclusion_cf_two_trigonal_structures_never_equivalent_closure_genus
      .first = 8 ∧
    conclusion_cf_two_trigonal_structures_never_equivalent_closure_genus
      .second = 10 ∧
    conclusion_cf_two_trigonal_structures_never_equivalent_branch_profile
      .first = [3, 3, 2, 2, 2, 2, 2, 2] ∧
    conclusion_cf_two_trigonal_structures_never_equivalent_branch_profile
      .second = List.replicate 10 2 ∧
    Omega.Folding.gaugeAnomalyTrigonalS3ClosureGenus = 8 ∧
    (10 * 3 - 6 * 2 + 2) / 2 = 10 ∧
    ¬ conclusion_cf_two_trigonal_structures_never_equivalent_cover_equivalent
        .first .second

/-- Paper label: `thm:conclusion-cf-two-trigonal-structures-never-equivalent`. -/
theorem paper_conclusion_cf_two_trigonal_structures_never_equivalent :
    conclusion_cf_two_trigonal_structures_never_equivalent_statement := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact Omega.Folding.paper_fold_gauge_anomaly_first_trigonal_monodromy_genus.2.2
  · exact Omega.Folding.GaugeAnomalyTrigonalGenus.riemann_hurwitz_genus
  · intro h
    exact (by decide :
      ¬ ([3, 3, 2, 2, 2, 2, 2, 2] : List ℕ) = List.replicate 10 2) h.1

end Omega.Conclusion
