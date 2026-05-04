import Mathlib.Tactic
import Omega.Zeta.XiWindow6B3C3TightFrameFourthMomentNonsimilarity

namespace Omega.Zeta

/-- The transported short-root orbit for the window-`6` `B₃` multiplicity table. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots : List XiWindow6Root :=
  xiWindow6B3ShortRoots

/-- The transported long-root orbit for the window-`6` `B₃` multiplicity table. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots : List XiWindow6Root :=
  xiWindow6ShortRoots

/-- Transported fiber multiplicity table on the concrete `B₃` root dictionary. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity
    (root : XiWindow6Root) : ℕ :=
  if root = ((0 : ℤ), 1, 0) ∨ root = ((0 : ℤ), -1, 0) then 4
  else if root = ((1 : ℤ), -1, 0) ∨ root = ((-1 : ℤ), -1, 0) then 3
  else if root = ((-1 : ℤ), 1, 0) ∨ root = ((0 : ℤ), 1, 1) then 4
  else 2

/-- A multiplicity value occurs on a listed root orbit. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
    (roots : List XiWindow6Root) (value : ℕ) : Prop :=
  ∃ root ∈ roots,
    xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity root = value

/-- The transported multiplicity is not constant on a listed root orbit. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_nonconstant_on
    (roots : List XiWindow6Root) : Prop :=
  ∃ rootA ∈ roots, ∃ rootB ∈ roots,
    xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity rootA ≠
      xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity rootB

/-- Concrete window-`6` `B₃` Weyl-breaking certificate. -/
def xi_window6_fiber_multiplicity_weyl_breaking_b3_statement : Prop :=
  xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots = xiWindow6B3ShortRoots ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots = xiWindow6ShortRoots ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
      xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots 2 ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
      xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots 4 ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
      xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots 2 ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
      xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots 3 ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_value_occurs
      xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots 4 ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_nonconstant_on
      xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots ∧
    xi_window6_fiber_multiplicity_weyl_breaking_b3_nonconstant_on
      xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots

/-- Paper label: `thm:xi-window6-fiber-multiplicity-weyl-breaking-b3`. -/
theorem paper_xi_window6_fiber_multiplicity_weyl_breaking_b3 :
    xi_window6_fiber_multiplicity_weyl_breaking_b3_statement := by
  unfold xi_window6_fiber_multiplicity_weyl_breaking_b3_statement
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨((1 : ℤ), 0, 0), by
      simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots,
        xiWindow6B3ShortRoots], by
      norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]⟩
  · exact ⟨((0 : ℤ), 1, 0), by
      simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots,
        xiWindow6B3ShortRoots], by
      norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]⟩
  · exact ⟨((1 : ℤ), 1, 0), by
      simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots, xiWindow6ShortRoots], by
      norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]⟩
  · exact ⟨((1 : ℤ), -1, 0), by
      simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots, xiWindow6ShortRoots], by
      norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]⟩
  · exact ⟨((-1 : ℤ), 1, 0), by
      simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots, xiWindow6ShortRoots], by
      norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]⟩
  · refine ⟨((1 : ℤ), 0, 0), ?_, ((0 : ℤ), 1, 0), ?_, ?_⟩
    · simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots, xiWindow6B3ShortRoots]
    · simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_short_roots, xiWindow6B3ShortRoots]
    · norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]
  · refine ⟨((1 : ℤ), 1, 0), ?_, ((1 : ℤ), -1, 0), ?_, ?_⟩
    · simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots, xiWindow6ShortRoots]
    · simp [xi_window6_fiber_multiplicity_weyl_breaking_b3_long_roots, xiWindow6ShortRoots]
    · norm_num [xi_window6_fiber_multiplicity_weyl_breaking_b3_transported_multiplicity]

end Omega.Zeta
