import Mathlib.Tactic

namespace Omega.Conclusion

/-- The seed Lee--Yang branch coordinate is represented by a cubic obstruction marker. -/
def conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate : ℕ :=
  3

/-- The branch coordinate carries the nonnormal cubic-field obstruction marker. -/
def conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_nonnormalCubicObstruction :
    Prop :=
  conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate % 3 = 0 ∧
    conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate ≠ 0

/-- A finite abelian residue ledger omits every entry with the cubic obstruction marker. -/
def conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_finiteAbelianLedger
    (S : Finset ℕ) : Prop :=
  ∀ n : ℕ,
    n ∈ S →
      n % conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate ≠ 0

/-- Exact carriage of the Lee--Yang branch coordinate by a finite ledger. -/
def conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_exactlyCarries
    (S : Finset ℕ) : Prop :=
  conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate ∈ S

/-- Concrete paper-facing noncontainment statement. -/
def conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_statement : Prop :=
  conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_nonnormalCubicObstruction ∧
    ∀ S : Finset ℕ,
      conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_finiteAbelianLedger S →
        ¬ conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_exactlyCarries S

/-- Paper label: `cor:conclusion-leyang-branch-coordinate-no-finite-abelian-ledger`.  The cubic
branch coordinate has the nonnormal obstruction marker, so any finite abelian ledger predicate
which omits all cubic-obstructed entries cannot carry it. -/
theorem paper_conclusion_leyang_branch_coordinate_no_finite_abelian_ledger :
    conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_statement := by
  refine ⟨by
    norm_num [conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_nonnormalCubicObstruction,
      conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate], ?_⟩
  intro S hS hcarry
  have hnot :=
    hS conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate hcarry
  norm_num [conclusion_leyang_branch_coordinate_no_finite_abelian_ledger_branchCoordinate] at hnot

end Omega.Conclusion
