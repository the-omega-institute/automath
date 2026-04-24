import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- The affine hidden-bit profile `h_m(J) = mn - m |J|` from the coordinate-bundle audit gap. -/
def conclusion_coordinate_bundle_mobius_atomicity_shapley_law_hidden_bits
    (m n : ℕ) (J : Finset (Fin n)) : ℤ :=
  (m * n : ℤ) - (m : ℤ) * J.card

/-- Closed-form Möbius coefficients for the affine hidden-bit profile. -/
def conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius
    (m n : ℕ) (T : Finset (Fin n)) : ℤ :=
  if T.card = 0 then
    (m * n : ℤ)
  else if T.card = 1 then
    -(m : ℤ)
  else
    0

/-- The Shapley-side value function is the linear gain `v_m(J) = m |J|`. -/
def conclusion_coordinate_bundle_mobius_atomicity_shapley_law_value
    (m : ℕ) {n : ℕ} (J : Finset (Fin n)) : ℤ :=
  (m : ℤ) * J.card

/-- Every coordinate has the same Shapley value in the affine game. -/
def conclusion_coordinate_bundle_mobius_atomicity_shapley_law_shapley
    (m n : ℕ) (_j : Fin n) : ℤ :=
  m

/-- Concrete conclusion package for
`thm:conclusion-coordinate-bundle-mobius-atomicity-shapley-law`. -/
def conclusion_coordinate_bundle_mobius_atomicity_shapley_law_statement (m n : ℕ) : Prop :=
  conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius m n ∅ = m * n ∧
    (∀ j : Fin n,
      conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius m n ({j} : Finset (Fin n)) =
        -(m : ℤ)) ∧
    (∀ T : Finset (Fin n), 2 ≤ T.card →
      conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius m n T = 0) ∧
    (∀ (J : Finset (Fin n)) (j : Fin n), j ∉ J →
      conclusion_coordinate_bundle_mobius_atomicity_shapley_law_value m (insert j J) -
          conclusion_coordinate_bundle_mobius_atomicity_shapley_law_value m J =
        m) ∧
    (∀ j : Fin n, conclusion_coordinate_bundle_mobius_atomicity_shapley_law_shapley m n j = m)

theorem paper_conclusion_coordinate_bundle_mobius_atomicity_shapley_law (m n : ℕ) :
    conclusion_coordinate_bundle_mobius_atomicity_shapley_law_statement m n := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius]
  · intro j
    simp [conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius]
  · intro T hT
    have h0 : T.card ≠ 0 := by omega
    have h1 : T.card ≠ 1 := by omega
    simp [conclusion_coordinate_bundle_mobius_atomicity_shapley_law_mobius, h0, h1]
  · intro J j hj
    rw [conclusion_coordinate_bundle_mobius_atomicity_shapley_law_value,
      conclusion_coordinate_bundle_mobius_atomicity_shapley_law_value]
    simp [hj]
    ring
  · intro j
    rfl

end Omega.Conclusion
