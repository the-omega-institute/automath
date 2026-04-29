import Mathlib.Tactic

namespace Omega.Zeta

/-- Six-bit words used in the audited window-`6` center split. -/
abbrev xi_window6_center_exact_splitting_bdry_cyclic_word := String

/-- The three boundary words in the two-fiber center layer. -/
def xi_window6_center_exact_splitting_bdry_cyclic_boundary_two_fiber_words :
    List xi_window6_center_exact_splitting_bdry_cyclic_word :=
  ["100001", "100101", "101001"]

/-- The five cyclic words in the two-fiber center layer. -/
def xi_window6_center_exact_splitting_bdry_cyclic_cyclic_two_fiber_words :
    List xi_window6_center_exact_splitting_bdry_cyclic_word :=
  ["000001", "000101", "001001", "010001", "010101"]

/-- The complete two-fiber list, ordered as cyclic words followed by boundary words. -/
def xi_window6_center_exact_splitting_bdry_cyclic_two_fiber_words :
    List xi_window6_center_exact_splitting_bdry_cyclic_word :=
  xi_window6_center_exact_splitting_bdry_cyclic_cyclic_two_fiber_words ++
    xi_window6_center_exact_splitting_bdry_cyclic_boundary_two_fiber_words

/-- The audited complete two-fiber word list. -/
def xi_window6_center_exact_splitting_bdry_cyclic_expected_two_fiber_words :
    List xi_window6_center_exact_splitting_bdry_cyclic_word :=
  ["000001", "000101", "001001", "010001", "010101", "100001", "100101", "101001"]

/-- The audited cyclic two-fiber word list. -/
def xi_window6_center_exact_splitting_bdry_cyclic_expected_cyclic_two_fiber_words :
    List xi_window6_center_exact_splitting_bdry_cyclic_word :=
  ["000001", "000101", "001001", "010001", "010101"]

/-- Boundary center rank contributed by the boundary two-fiber words. -/
def xi_window6_center_exact_splitting_bdry_cyclic_boundary_rank : ℕ :=
  xi_window6_center_exact_splitting_bdry_cyclic_boundary_two_fiber_words.length

/-- Cyclic center rank contributed by the cyclic two-fiber words. -/
def xi_window6_center_exact_splitting_bdry_cyclic_cyclic_rank : ℕ :=
  xi_window6_center_exact_splitting_bdry_cyclic_cyclic_two_fiber_words.length

/-- Total center rank in the window-`6` center. -/
def xi_window6_center_exact_splitting_bdry_cyclic_center_rank : ℕ :=
  xi_window6_center_exact_splitting_bdry_cyclic_boundary_rank +
    xi_window6_center_exact_splitting_bdry_cyclic_cyclic_rank

/-- Paper label: `thm:xi-window6-center-exact-splitting-bdry-cyclic`. -/
theorem paper_xi_window6_center_exact_splitting_bdry_cyclic :
    xi_window6_center_exact_splitting_bdry_cyclic_two_fiber_words =
      xi_window6_center_exact_splitting_bdry_cyclic_expected_two_fiber_words ∧
    xi_window6_center_exact_splitting_bdry_cyclic_cyclic_two_fiber_words =
      xi_window6_center_exact_splitting_bdry_cyclic_expected_cyclic_two_fiber_words ∧
    xi_window6_center_exact_splitting_bdry_cyclic_boundary_rank = 3 ∧
    xi_window6_center_exact_splitting_bdry_cyclic_cyclic_rank = 5 ∧
    xi_window6_center_exact_splitting_bdry_cyclic_center_rank = 8 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

end Omega.Zeta
