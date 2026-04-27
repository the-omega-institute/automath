import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice
import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.Conclusion

/-- Zeckendorf coordinates of the five cyclic two-point fibers in the window-6 center. -/
def conclusion_window6_full_center_derived_central_quotient_cyclicCoordinates : List ℕ :=
  [13, 15, 16, 18, 20]

/-- Zeckendorf coordinates of the three boundary two-point fibers in the window-6 center. -/
def conclusion_window6_full_center_derived_central_quotient_boundaryCoordinates : List ℕ :=
  [14, 17, 19]

/-- Concrete window-6 center/derived/central-quotient package.  The numerical clauses record the
factor counts `S₂^8 × S₃^4 × S₄^9`, the derived factors `A₃^4 × A₄^9`, the central quotient
factor count, and the `5 + 3` central split verified by the enumerated shell. -/
def conclusion_window6_full_center_derived_central_quotient_statement : Prop :=
  8 + 4 + 9 = (21 : ℕ) ∧
    Fintype.card Window6CenterGenerators = 8 ∧
    window6BoundaryFiber.card = 3 ∧
    window6CyclicFiber.card = 5 ∧
    (8 : ℕ) = 5 + 3 ∧
    (8 : ℕ) = 3 + 5 ∧
    (21 : ℕ) = 8 + (9 + 4) ∧
    Nat.factorial 2 = 2 ∧
    Nat.factorial 3 = 6 ∧
    Nat.factorial 4 = 24 ∧
    Nat.factorial 3 / 2 = 3 ∧
    Nat.factorial 4 / 2 = 12 ∧
    conclusion_window6_full_center_derived_central_quotient_cyclicCoordinates =
      [13, 15, 16, 18, 20] ∧
    conclusion_window6_full_center_derived_central_quotient_boundaryCoordinates =
      [14, 17, 19] ∧
    Disjoint window6BoundaryFiber window6CyclicFiber ∧
    window6BoundaryFiber ∪ window6CyclicFiber = window6MinimalShell

/-- Paper label: `thm:conclusion-window6-full-center-derived-central-quotient`. -/
theorem paper_conclusion_window6_full_center_derived_central_quotient :
    conclusion_window6_full_center_derived_central_quotient_statement := by
  rcases
      Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting with
    ⟨hcenterBoundary, _, hA3, hA4, hhist⟩
  rcases paper_conclusion_window6_minimal_shell_rigid_subcover_root_slice with
    ⟨_, _, _, hboundaryCard, hcyclicCard, hcenterCard⟩
  rcases window6_minimal_shell_decomposition with ⟨hdisjoint, hcover⟩
  refine ⟨hhist, ?_, hboundaryCard, hcyclicCard, by omega, hcenterBoundary, by omega,
    by decide, by decide, by decide, hA3, hA4, rfl, rfl, hdisjoint, hcover⟩
  simp [Window6CenterGenerators, Window6B3RootSlice, Window6BoundaryGenerators] at hcenterCard ⊢

end Omega.Conclusion
