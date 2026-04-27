import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldbinCoinvariantGorenstein

namespace Omega.Conclusion

/-- The numerator for an `A₁` coinvariant factor, written as coefficients of `1 + t`. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_binary_numerator : List ℕ :=
  [1, 1]

/-- The numerator for an `A₂` coinvariant factor, written as coefficients of
`1 + t + t²`. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_ternary_numerator : List ℕ :=
  [1, 1, 1]

/-- The numerator for an `A₃` coinvariant factor, written as coefficients of
`1 + t + t² + t³`. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_quartic_numerator : List ℕ :=
  [1, 1, 1, 1]

/-- The window-`6` hidden coinvariant numerator-factor multiplicities. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_numerator_factors :
    List (ℕ × ℕ) :=
  [(1, 21), (2, 13), (3, 9)]

/-- The window-`6` hidden coinvariant total dimension. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_dimension : ℕ :=
  2 ^ 21 * 3 ^ 13 * 4 ^ 9

/-- The top degree of the window-`6` hidden coinvariant Hilbert polynomial. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_top_degree : ℕ :=
  21 * 1 + 13 * 2 + 9 * 3

/-- A coefficient-list form of polynomial palindromicity. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_palindromic (l : List ℕ) :
    Prop :=
  l.reverse = l

/-- Concrete Hilbert-series, dimension, top-degree, and palindrome package for the hidden
window-`6` coinvariant algebra. -/
def conclusion_window6_hidden_coinvariant_gorenstein_package_statement : Prop :=
  conclusion_window6_hidden_coinvariant_gorenstein_package_numerator_factors =
      [(1, 21), (2, 13), (3, 9)] ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_dimension = 2 ^ 39 * 3 ^ 13 ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_dimension =
      Omega.OperatorAlgebra.foldbinCoinvariantTotalDimensionSix ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_top_degree = 74 ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_top_degree =
      Omega.OperatorAlgebra.foldbinCoinvariantTopDegreeSix ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_palindromic
      conclusion_window6_hidden_coinvariant_gorenstein_package_binary_numerator ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_palindromic
      conclusion_window6_hidden_coinvariant_gorenstein_package_ternary_numerator ∧
    conclusion_window6_hidden_coinvariant_gorenstein_package_palindromic
      conclusion_window6_hidden_coinvariant_gorenstein_package_quartic_numerator

/-- Paper label: `thm:conclusion-window6-hidden-coinvariant-gorenstein-package`.

The factor list is the `m = 6` specialization of the foldbin coinvariant package. Dimension and
top degree reduce to the audited arithmetic normal forms, while the three numerator factors are
palindromic coefficient lists. -/
theorem paper_conclusion_window6_hidden_coinvariant_gorenstein_package :
    conclusion_window6_hidden_coinvariant_gorenstein_package_statement := by
  rcases Omega.OperatorAlgebra.paper_foldbin_coinvariant_gorenstein 6 with
    ⟨_hdecomp, _hcount, _hdim_general, _htop_general, hsix⟩
  rcases hsix rfl with ⟨hseries, _hfactorial, hdim_six, htop_six⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hseries
  · native_decide
  · rw [conclusion_window6_hidden_coinvariant_gorenstein_package_dimension, hdim_six]
    native_decide
  · native_decide
  · rw [conclusion_window6_hidden_coinvariant_gorenstein_package_top_degree, htop_six]
  · rfl
  · rfl
  · rfl

end Omega.Conclusion
