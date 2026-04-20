import Mathlib.Tactic
import Omega.GU.Window6C3SupportCount

namespace Omega.GU

open Finset

/-- Exponent triples for monomials in `ℚ[x₁, x₂, x₃]`. -/
abbrev Window6C3Exponent := ℕ × ℕ × ℕ

/-- The lex initial ideal from the `C₃` support computation. -/
def window6C3InitialIdealGeneratorExponents : Finset Window6C3Exponent :=
  ([((3 : ℕ), 0, 0), (2, 1, 0), (2, 0, 1), (1, 3, 0), (1, 1, 1), (1, 0, 3), (0, 5, 0),
    (0, 3, 1), (0, 1, 3), (0, 0, 5)] : List Window6C3Exponent).toFinset

/-- The `19` standard monomials listed in the paper for the `C₃` packet. -/
def window6C3StandardMonomials : Finset Window6C3Exponent :=
  ([((0 : ℕ), 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (2, 0, 0), (1, 1, 0), (1, 0, 1),
    (0, 2, 0), (0, 1, 1), (0, 0, 2), (1, 2, 0), (1, 0, 2), (0, 3, 0), (0, 2, 1), (0, 1, 2),
    (0, 0, 3), (0, 4, 0), (0, 2, 2), (0, 0, 4)] : List Window6C3Exponent).toFinset

/-- Total degree on exponent triples. -/
def window6C3TotalDegree (e : Window6C3Exponent) : ℕ :=
  e.1 + e.2.1 + e.2.2

/-- Hilbert coefficient obtained by counting standard monomials of total degree `d`. -/
def window6C3HilbertCoefficient (d : ℕ) : ℕ :=
  (window6C3StandardMonomials.filter (fun e => window6C3TotalDegree e = d)).card

/-- Concrete package for the window-`6` `C₃` vanishing-ideal/Hilbert-series computation. -/
def window6C3SupportVanishingIdealHilbertStatement : Prop :=
  Omega.GU.Window6C3SupportCount.c3Support.card = 19 ∧
    window6C3InitialIdealGeneratorExponents.card = 10 ∧
    window6C3StandardMonomials.card = 19 ∧
    window6C3HilbertCoefficient 0 = 1 ∧
    window6C3HilbertCoefficient 1 = 3 ∧
    window6C3HilbertCoefficient 2 = 6 ∧
    window6C3HilbertCoefficient 3 = 6 ∧
    window6C3HilbertCoefficient 4 = 3 ∧
    window6C3HilbertCoefficient 5 = 0 ∧
    window6C3StandardMonomials.card = Omega.GU.Window6C3SupportCount.c3Support.card

/-- Paper label: `thm:window6-c3-support-vanishing-ideal-hilbert`. -/
theorem paper_window6_c3_support_vanishing_ideal_hilbert :
    window6C3SupportVanishingIdealHilbertStatement := by
  refine ⟨Omega.GU.Window6C3SupportCount.c3Support_card, by native_decide, by native_decide,
    by native_decide, by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, ?_⟩
  rw [Omega.GU.Window6C3SupportCount.c3Support_card]
  native_decide

end Omega.GU
