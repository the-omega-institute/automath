import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Omega.Conclusion.CoordinateBundlePosteriorHypercubeFactorization

namespace Omega.Conclusion

/-- Concrete pair of slab coordinates in the posterior hypercube. -/
abbrev conclusion_coordinate_bundle_posterior_slab_rigidity_data :=
  Σ L : ℕ, Fin L × Fin L

/-- First slab coordinate. -/
def conclusion_coordinate_bundle_posterior_slab_rigidity_left
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) : Fin D.1 :=
  D.2.1

/-- Second slab coordinate. -/
def conclusion_coordinate_bundle_posterior_slab_rigidity_right
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) : Fin D.1 :=
  D.2.2

/-- The centered bit read from a slab coordinate. -/
def conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) (ε : Fin D.1 → ZMod 2)
    (i : Fin D.1) : ZMod 2 :=
  ε i

/-- Different slabs read independent product coordinates: every pair of bit values is realized. -/
def conclusion_coordinate_bundle_posterior_slab_rigidity_pairRealizable
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) : Prop :=
  ∀ a b : ZMod 2, ∃ ε : Fin D.1 → ZMod 2,
    conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit D ε
        (conclusion_coordinate_bundle_posterior_slab_rigidity_left D) = a ∧
      conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit D ε
        (conclusion_coordinate_bundle_posterior_slab_rigidity_right D) = b

/-- Concrete slab-rigidity statement for the coordinate-product posterior. -/
def conclusion_coordinate_bundle_posterior_slab_rigidity_statement
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) : Prop :=
  (conclusion_coordinate_bundle_posterior_slab_rigidity_left D =
      conclusion_coordinate_bundle_posterior_slab_rigidity_right D →
    ∀ ε : Fin D.1 → ZMod 2,
      conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit D ε
          (conclusion_coordinate_bundle_posterior_slab_rigidity_left D) =
        conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit D ε
          (conclusion_coordinate_bundle_posterior_slab_rigidity_right D)) ∧
    (conclusion_coordinate_bundle_posterior_slab_rigidity_left D ≠
        conclusion_coordinate_bundle_posterior_slab_rigidity_right D →
      conclusion_coordinate_bundle_posterior_slab_rigidity_pairRealizable D)

/-- Paper label: `cor:conclusion-coordinate-bundle-posterior-slab-rigidity`. -/
theorem paper_conclusion_coordinate_bundle_posterior_slab_rigidity
    (D : conclusion_coordinate_bundle_posterior_slab_rigidity_data) :
    conclusion_coordinate_bundle_posterior_slab_rigidity_statement D := by
  constructor
  · intro hsame ε
    simp [conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit, hsame]
  · intro hdiff a b
    let i := conclusion_coordinate_bundle_posterior_slab_rigidity_left D
    let j := conclusion_coordinate_bundle_posterior_slab_rigidity_right D
    let ε : Fin D.1 → ZMod 2 := fun k => if k = i then a else if k = j then b else 0
    refine ⟨ε, ?_, ?_⟩
    · simp [conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit, ε, i]
    · have hji : j ≠ i := by
        dsimp [i, j] at hdiff ⊢
        exact fun h => hdiff h.symm
      simp [conclusion_coordinate_bundle_posterior_slab_rigidity_centeredBit, ε, i, j, hji]

end Omega.Conclusion
