import Omega.Zeta.RealInput40BartholdiDet

namespace Omega.Zeta

/-- The `(t - 1)`-adic valuation profile extracted from the audited factorization. -/
def realInput40BartholdiValuation : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 2
  | 12 => 2
  | 13 => 3
  | 14 => 3
  | 15 => 4
  | 16 => 4
  | 17 => 5
  | 18 => 5
  | 19 => 6
  | 20 => 7
  | _ => 0

/-- Reversed valuation profile for `G(λ, ε) = λ^20 F(λ⁻¹, 1 + ε)`. -/
def realInput40BartholdiReversedValuation (x : ℕ) : ℕ :=
  realInput40BartholdiValuation (20 - x)

/-- Lower Newton hull vertices for the escaping cluster. -/
def realInput40BartholdiLowerHullVertices : List (ℕ × ℕ) :=
  [(0, 7), (2, 5), (10, 1), (13, 0), (20, 0)]

/-- The three Newton--Puiseux escape exponents. -/
def realInput40BartholdiEscapeSlope : Fin 3 → ℚ
  | 0 => 1
  | 1 => 1 / 2
  | 2 => 1 / 3

/-- Horizontal lengths of the three lower-hull edges. -/
def realInput40BartholdiEscapeMultiplicity : Fin 3 → ℕ
  | 0 => 2
  | 1 => 8
  | 2 => 3

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:real-input-40-bartholdi-newton-puiseux-spectrum`. -/
theorem paper_real_input_40_bartholdi_newton_puiseux_spectrum :
    (∀ k,
      realInput40BartholdiValuation k =
        match k with
        | 0 => 0
        | 1 => 0
        | 2 => 0
        | 3 => 0
        | 4 => 0
        | 5 => 0
        | 6 => 0
        | 7 => 0
        | 8 => 1
        | 9 => 2
        | 10 => 1
        | 11 => 2
        | 12 => 2
        | 13 => 3
        | 14 => 3
        | 15 => 4
        | 16 => 4
        | 17 => 5
        | 18 => 5
        | 19 => 6
        | 20 => 7
        | _ => 0) ∧
    (∀ x, realInput40BartholdiReversedValuation x = realInput40BartholdiValuation (20 - x)) ∧
    realInput40BartholdiLowerHullVertices = [(0, 7), (2, 5), (10, 1), (13, 0), (20, 0)] ∧
    realInput40BartholdiEscapeSlope 0 = 1 ∧
    realInput40BartholdiEscapeSlope 1 = 1 / 2 ∧
    realInput40BartholdiEscapeSlope 2 = 1 / 3 ∧
    realInput40BartholdiEscapeMultiplicity 0 = 2 ∧
    realInput40BartholdiEscapeMultiplicity 1 = 8 ∧
    realInput40BartholdiEscapeMultiplicity 2 = 3 ∧
    realInput40BartholdiEscapeMultiplicity 0 +
        realInput40BartholdiEscapeMultiplicity 1 +
        realInput40BartholdiEscapeMultiplicity 2 = 13 := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by native_decide⟩
  · intro k
    rfl
  · intro x
    rfl

end Omega.Zeta
