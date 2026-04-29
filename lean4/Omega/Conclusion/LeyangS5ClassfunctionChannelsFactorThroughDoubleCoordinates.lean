import Mathlib.Tactic

namespace Omega.Conclusion

universe u v w

/-- A concrete additive-affine predicate for the factor maps used in the two-channel coordinate
package.  The maps preserve the chosen origin and addition. -/
def conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_affine
    {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V → W) : Prop :=
  f 0 = 0 ∧ ∀ x y : V, f (x + y) = f x + f y

/-- Concrete data for the factorization of an `S₅` class-function channel through the double
coordinate map.  The coordinate map is packaged with an explicit inverse, and the channel and
inverse are additive-affine. -/
structure conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data where
  Domain : Type u
  Coordinates : Type v
  Codomain : Type w
  [instDomain : AddCommGroup Domain]
  [instCoordinates : AddCommGroup Coordinates]
  [instCodomain : AddCommGroup Codomain]
  M : Domain → Coordinates
  L : Domain → Codomain
  M_inv : Coordinates → Domain
  M_left_inverse : Function.LeftInverse M_inv M
  M_right_inverse : Function.RightInverse M_inv M
  L_affine :
    conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_affine L
  M_inv_affine :
    conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_affine M_inv

attribute [instance]
  conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.instDomain
attribute [instance]
  conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.instCoordinates
attribute [instance]
  conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.instCodomain

namespace conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data

/-- The factor map is the class-function channel composed with the inverse coordinate map. -/
def factorMap
    (D : conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data) :
    D.Coordinates → D.Codomain :=
  fun y => D.L (D.M_inv y)

/-- Existence and uniqueness of the affine factorization through the double coordinates. -/
def existsUniqueAffineFactorization
    (D : conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data) :
    Prop :=
  ∃ Φ : D.Coordinates → D.Codomain,
    conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_affine Φ ∧
      D.L = Φ ∘ D.M ∧
        ∀ Ψ : D.Coordinates → D.Codomain,
          conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_affine Ψ →
            D.L = Ψ ∘ D.M → Ψ = Φ

end conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data

/-- Paper label:
`thm:conclusion-leyang-s5-classfunction-channels-factor-through-double-coordinates`.

The inverse of the double-coordinate map turns any affine class-function channel into a unique
affine map on coordinates, with uniqueness following from surjectivity of the coordinate map. -/
theorem paper_conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates
    (D : conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data) :
    D.existsUniqueAffineFactorization := by
  refine ⟨D.factorMap, ?_, ?_, ?_⟩
  · constructor
    · simp [conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.factorMap,
        D.M_inv_affine.1, D.L_affine.1]
    · intro x y
      simp [conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.factorMap,
        D.M_inv_affine.2 x y, D.L_affine.2]
  · funext x
    simp [Function.comp_apply,
      conclusion_leyang_s5_classfunction_channels_factor_through_double_coordinates_data.factorMap,
      D.M_left_inverse x]
  · intro Ψ _hΨ hfactor
    funext y
    have hy : D.M (D.M_inv y) = y := D.M_right_inverse y
    calc
      Ψ y = Ψ (D.M (D.M_inv y)) := by rw [hy]
      _ = (Ψ ∘ D.M) (D.M_inv y) := rfl
      _ = D.L (D.M_inv y) := by
        exact (congrFun hfactor (D.M_inv y)).symm
      _ = D.factorMap y := rfl

end Omega.Conclusion
