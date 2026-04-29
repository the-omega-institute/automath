import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite data for the second-order refined collision uniformization identity. -/
structure conclusion_second_order_refined_collision_weighted_uniformization_data where
  conclusion_second_order_refined_collision_weighted_uniformization_fiber : Type
  conclusion_second_order_refined_collision_weighted_uniformization_label : Type
  conclusion_second_order_refined_collision_weighted_uniformization_fiber_fintype :
    Fintype conclusion_second_order_refined_collision_weighted_uniformization_fiber
  conclusion_second_order_refined_collision_weighted_uniformization_label_fintype :
    Fintype conclusion_second_order_refined_collision_weighted_uniformization_label
  conclusion_second_order_refined_collision_weighted_uniformization_weight :
    conclusion_second_order_refined_collision_weighted_uniformization_fiber → ℝ
  conclusion_second_order_refined_collision_weighted_uniformization_mass : ℝ
  conclusion_second_order_refined_collision_weighted_uniformization_local :
    conclusion_second_order_refined_collision_weighted_uniformization_fiber →
      conclusion_second_order_refined_collision_weighted_uniformization_label → ℝ
  conclusion_second_order_refined_collision_weighted_uniformization_label_card_pos :
    0 < Fintype.card conclusion_second_order_refined_collision_weighted_uniformization_label

namespace conclusion_second_order_refined_collision_weighted_uniformization_data

/-- The weighted local `L²` non-uniformity field. -/
noncomputable def conclusion_second_order_refined_collision_weighted_uniformization_l2_field
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data)
    (x : D.conclusion_second_order_refined_collision_weighted_uniformization_fiber) : ℝ :=
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_label_fintype
  let n : ℝ :=
    (Fintype.card D.conclusion_second_order_refined_collision_weighted_uniformization_label : ℝ)
  ∑ g, (D.conclusion_second_order_refined_collision_weighted_uniformization_local x g - n⁻¹) ^ 2

/-- Collision-escort expectation of a local scalar field. -/
noncomputable def conclusion_second_order_refined_collision_weighted_uniformization_expect
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data)
    (F : D.conclusion_second_order_refined_collision_weighted_uniformization_fiber → ℝ) : ℝ :=
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_fiber_fintype
  ∑ x,
    (D.conclusion_second_order_refined_collision_weighted_uniformization_weight x /
      D.conclusion_second_order_refined_collision_weighted_uniformization_mass) * F x

/-- Packaged finite Plancherel field: nontrivial Fourier energy is `|G|` times local `L²`
non-uniformity. -/
noncomputable def conclusion_second_order_refined_collision_weighted_uniformization_fourier_energy
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data)
    (x : D.conclusion_second_order_refined_collision_weighted_uniformization_fiber) : ℝ :=
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_label_fintype
  (Fintype.card D.conclusion_second_order_refined_collision_weighted_uniformization_label : ℝ) *
    conclusion_second_order_refined_collision_weighted_uniformization_l2_field D x

/-- Refined `q = 2` collision ratio after adjoining the uniform floor. -/
noncomputable def conclusion_second_order_refined_collision_weighted_uniformization_refined_ratio
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data) : ℝ :=
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_label_fintype
  let n : ℝ :=
    (Fintype.card D.conclusion_second_order_refined_collision_weighted_uniformization_label : ℝ)
  n⁻¹ +
    conclusion_second_order_refined_collision_weighted_uniformization_expect D
      (conclusion_second_order_refined_collision_weighted_uniformization_l2_field D)

/-- Paper-facing statement: the excess over the uniform floor is both weighted local
non-uniformity and weighted nontrivial Fourier energy. -/
def conclusion_second_order_refined_collision_weighted_uniformization_statement
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data) : Prop :=
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_label_fintype
  let n : ℝ :=
    (Fintype.card D.conclusion_second_order_refined_collision_weighted_uniformization_label : ℝ)
  conclusion_second_order_refined_collision_weighted_uniformization_refined_ratio D - n⁻¹ =
      conclusion_second_order_refined_collision_weighted_uniformization_expect D
        (conclusion_second_order_refined_collision_weighted_uniformization_l2_field D) ∧
    conclusion_second_order_refined_collision_weighted_uniformization_refined_ratio D - n⁻¹ =
      n⁻¹ *
        conclusion_second_order_refined_collision_weighted_uniformization_expect D
          (conclusion_second_order_refined_collision_weighted_uniformization_fourier_energy D)

end conclusion_second_order_refined_collision_weighted_uniformization_data

open conclusion_second_order_refined_collision_weighted_uniformization_data

/-- Paper label: `thm:conclusion-second-order-refined-collision-weighted-uniformization`. -/
theorem paper_conclusion_second_order_refined_collision_weighted_uniformization
    (D : conclusion_second_order_refined_collision_weighted_uniformization_data) :
    conclusion_second_order_refined_collision_weighted_uniformization_statement D := by
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_fiber_fintype
  letI := D.conclusion_second_order_refined_collision_weighted_uniformization_label_fintype
  have hn :
      (Fintype.card
        D.conclusion_second_order_refined_collision_weighted_uniformization_label : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        D.conclusion_second_order_refined_collision_weighted_uniformization_label_card_pos)
  unfold conclusion_second_order_refined_collision_weighted_uniformization_statement
  dsimp [conclusion_second_order_refined_collision_weighted_uniformization_refined_ratio,
    conclusion_second_order_refined_collision_weighted_uniformization_expect,
    conclusion_second_order_refined_collision_weighted_uniformization_fourier_energy]
  refine ⟨?_, ?_⟩
  · ring
  · rw [Finset.mul_sum]
    field_simp [hn]
    ring

end Omega.Conclusion
