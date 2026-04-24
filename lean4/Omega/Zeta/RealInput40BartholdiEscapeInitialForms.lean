import Omega.Zeta.RealInput40BartholdiNewtonPuiseuxSpectrum
import Mathlib.Tactic

namespace Omega.Zeta

/-- Initial form on the `α = 1` Newton edge. -/
def realInput40BartholdiAlphaOneInitialForm (ξ : ℤ) : ℤ :=
  ξ ^ 2 + 1

/-- Reduced quartic after writing the `α = 1/2` initial form in the even variable `y = ξ²`. -/
def realInput40BartholdiAlphaHalfInitialForm (y : ℤ) : ℤ :=
  y ^ 4 - 4 * y ^ 3 + 7 * y ^ 2 - 6 * y + 2

/-- Full `α = 1/2` initial form before factoring out the shared zero root. -/
def realInput40BartholdiAlphaHalfXiInitialForm (ξ : ℤ) : ℤ :=
  -4 * ξ ^ 2 + 12 * ξ ^ 4 - 14 * ξ ^ 6 + 8 * ξ ^ 8 - 2 * ξ ^ 10

/-- Initial form on the `α = 1/3` Newton edge. -/
def realInput40BartholdiAlphaThirdInitialForm (ξ : ℤ) : ℤ :=
  ξ ^ 3 - 2

/-- Paper label: `prop:real-input-40-bartholdi-escape-initial-forms`.
The three lower-hull edges from the Newton--Puiseux spectrum produce the explicit initial-form
polynomials `ξ² + 1`, `ξ³ - 2`, and the even quartic package for `y = ξ²`. -/
theorem paper_real_input_40_bartholdi_escape_initial_forms :
    realInput40BartholdiLowerHullVertices = [(0, 7), (2, 5), (10, 1), (13, 0), (20, 0)] ∧
      realInput40BartholdiEscapeSlope 0 = 1 ∧
      (∀ ξ, realInput40BartholdiAlphaOneInitialForm ξ = ξ ^ 2 + 1) ∧
      realInput40BartholdiEscapeMultiplicity 0 = 2 ∧
      realInput40BartholdiEscapeSlope 1 = 1 / 2 ∧
      (∀ y, realInput40BartholdiAlphaHalfInitialForm y = y ^ 4 - 4 * y ^ 3 + 7 * y ^ 2 - 6 * y + 2) ∧
      (∀ ξ, realInput40BartholdiAlphaHalfXiInitialForm ξ =
        -2 * ξ ^ 2 * realInput40BartholdiAlphaHalfInitialForm (ξ ^ 2)) ∧
      realInput40BartholdiEscapeMultiplicity 1 = 8 ∧
      realInput40BartholdiEscapeSlope 2 = 1 / 3 ∧
      (∀ ξ, realInput40BartholdiAlphaThirdInitialForm ξ = ξ ^ 3 - 2) ∧
      realInput40BartholdiEscapeMultiplicity 2 = 3 ∧
      realInput40BartholdiEscapeMultiplicity 0 +
          realInput40BartholdiEscapeMultiplicity 1 +
          realInput40BartholdiEscapeMultiplicity 2 = 13 := by
  rcases paper_real_input_40_bartholdi_newton_puiseux_spectrum with
    ⟨_, _, hverts, hs0, hs1, hs2, hm0, hm1, hm2, hsum⟩
  refine ⟨hverts, hs0, ?_, hm0, hs1, ?_, ?_, hm1, hs2, ?_, hm2, hsum⟩
  · intro ξ
    rfl
  · intro y
    rfl
  · intro ξ
    simp [realInput40BartholdiAlphaHalfXiInitialForm, realInput40BartholdiAlphaHalfInitialForm]
    ring
  · intro ξ
    rfl

end Omega.Zeta
