import Mathlib

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete finite-state time-image data: a finite family of edge labels and an additive
time map on generated morphisms. -/
structure xi_finite_state_time_image_discrete_or_dense_data where
  edgeCount : ℕ
  edgeTime : Fin edgeCount → ℝ
  morphismTime : (Fin edgeCount → ℤ) → ℝ
  morphismTime_eq_integerCombination :
    ∀ c : Fin edgeCount → ℤ, morphismTime c = ∑ e : Fin edgeCount, (c e : ℝ) * edgeTime e
  integerSpan_dichotomy :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ,
        x ∈ Set.range (fun c : Fin edgeCount → ℤ =>
          ∑ e : Fin edgeCount, (c e : ℝ) * edgeTime e) →
        x ≠ 0 → δ ≤ |x|) ∨
      Dense (Set.range (fun c : Fin edgeCount → ℤ =>
        ∑ e : Fin edgeCount, (c e : ℝ) * edgeTime e))

namespace xi_finite_state_time_image_discrete_or_dense_data

/-- Integer combination of the finite edge-time labels. -/
def integerCombination (D : xi_finite_state_time_image_discrete_or_dense_data)
    (c : Fin D.edgeCount → ℤ) : ℝ :=
  ∑ e : Fin D.edgeCount, (c e : ℝ) * D.edgeTime e

/-- The image of generated morphisms under the additive time map. -/
def timeImage (D : xi_finite_state_time_image_discrete_or_dense_data) : Set ℝ :=
  Set.range D.morphismTime

/-- The integer span of the finite set of edge-time labels. -/
def integerSpan (D : xi_finite_state_time_image_discrete_or_dense_data) : Set ℝ :=
  Set.range D.integerCombination

/-- The generated time image is contained in the integer span of edge labels. -/
def timeImageContainedInIntegerSpan
    (D : xi_finite_state_time_image_discrete_or_dense_data) : Prop :=
  D.timeImage ⊆ D.integerSpan

/-- Finite-generation certificate for the integer span. -/
def integerSpanFiniteGenerated (D : xi_finite_state_time_image_discrete_or_dense_data) : Prop :=
  ∃ generators : Finset ℝ,
    generators = Finset.univ.image D.edgeTime ∧ D.integerSpan = Set.range D.integerCombination

/-- Discrete real-subgroup branch: every nonzero span element has a uniform positive gap. -/
def integerSpanDiscrete (D : xi_finite_state_time_image_discrete_or_dense_data) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, x ∈ D.integerSpan → x ≠ 0 → δ ≤ |x|

/-- Dense real-subgroup branch for the integer span. -/
def integerSpanDense (D : xi_finite_state_time_image_discrete_or_dense_data) : Prop :=
  Dense D.integerSpan

/-- Countability of the generated time image. -/
def timeImageCountable (D : xi_finite_state_time_image_discrete_or_dense_data) : Prop :=
  D.timeImage.Countable

end xi_finite_state_time_image_discrete_or_dense_data

open xi_finite_state_time_image_discrete_or_dense_data

/-- Paper label: `prop:xi-finite-state-time-image-discrete-or-dense`. -/
theorem paper_xi_finite_state_time_image_discrete_or_dense
    (D : xi_finite_state_time_image_discrete_or_dense_data) :
    D.timeImageContainedInIntegerSpan ∧ D.integerSpanFiniteGenerated ∧
      (D.integerSpanDiscrete ∨ D.integerSpanDense) ∧ D.timeImageCountable := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    exact (D.morphismTime_eq_integerCombination c).symm
  · exact ⟨Finset.univ.image D.edgeTime, rfl, rfl⟩
  · simpa [integerSpanDiscrete, integerSpanDense, integerSpan, integerCombination] using
      D.integerSpan_dichotomy
  · simpa [timeImage] using Set.countable_range D.morphismTime

end Omega.Zeta
