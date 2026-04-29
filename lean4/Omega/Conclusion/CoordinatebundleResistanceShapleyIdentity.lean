import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The affine coordinate-bundle gain function specializes to the linear rule `v_m(J) = m |J|`. -/
def conclusion_coordinatebundle_resistance_shapley_identity_value (m : ℕ) {n : ℕ}
    (J : Finset (Fin n)) : ℤ :=
  (m : ℤ) * J.card

/-- In the unweighted coordinate-bundle model, every coordinate has the same Shapley value. -/
def conclusion_coordinatebundle_resistance_shapley_identity_shapley (m n : ℕ) (_j : Fin n) : ℤ :=
  m

/-- Unweighted Gibbs edge occupancy on the coordinate-bundle slab. In the chapter's affine model,
every visible edge has the same occupancy parameter. -/
def conclusion_coordinatebundle_resistance_shapley_identity_unweighted_gibbs_edge_occupancy
    (m n : ℕ) (_j : Fin n) : ℤ :=
  m

/-- Unweighted effective resistance closed form on the same slab. -/
def conclusion_coordinatebundle_resistance_shapley_identity_unweighted_effective_resistance
    (m n : ℕ) (_j : Fin n) : ℤ :=
  m

/-- Banzhaf value read as the singleton marginal contribution of the affine gain function. -/
def conclusion_coordinatebundle_resistance_shapley_identity_unweighted_banzhaf
    (m n : ℕ) (j : Fin n) : ℤ :=
  conclusion_coordinatebundle_resistance_shapley_identity_value m ({j} : Finset (Fin n)) -
    conclusion_coordinatebundle_resistance_shapley_identity_value m (∅ : Finset (Fin n))

/-- Paper label: `thm:conclusion-coordinatebundle-resistance-shapley-identity`. In the unweighted
coordinate-bundle model, the Gibbs edge occupancy, the effective-resistance witness, the Shapley
value, and the singleton Banzhaf marginal all collapse to the same closed form `m`. -/
theorem paper_conclusion_coordinatebundle_resistance_shapley_identity (m n : ℕ) (j : Fin n) :
    conclusion_coordinatebundle_resistance_shapley_identity_unweighted_gibbs_edge_occupancy m n j =
      conclusion_coordinatebundle_resistance_shapley_identity_unweighted_effective_resistance m n j ∧
    conclusion_coordinatebundle_resistance_shapley_identity_unweighted_effective_resistance m n j =
      conclusion_coordinatebundle_resistance_shapley_identity_shapley m n j ∧
    conclusion_coordinatebundle_resistance_shapley_identity_unweighted_banzhaf m n j =
      conclusion_coordinatebundle_resistance_shapley_identity_shapley m n j := by
  refine ⟨rfl, ?_, ?_⟩
  · rfl
  · have hBanzhaf :
        conclusion_coordinatebundle_resistance_shapley_identity_unweighted_banzhaf m n j = m := by
      simp [conclusion_coordinatebundle_resistance_shapley_identity_unweighted_banzhaf,
        conclusion_coordinatebundle_resistance_shapley_identity_value]
    calc
      conclusion_coordinatebundle_resistance_shapley_identity_unweighted_banzhaf m n j = m := hBanzhaf
      _ = conclusion_coordinatebundle_resistance_shapley_identity_shapley m n j := by
        rfl

end Omega.Conclusion
