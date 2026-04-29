import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete single-conductor pole data. Each finite fiber class has a pole radius and a pole
multiplicity; distinct classes have distinct radii. -/
structure conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data where
  conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count : ℕ
  conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius :
    Fin conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count → ℕ
  conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity :
    Fin conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count → ℕ
  conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius_injective :
    Function.Injective conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius

/-- Histogram recovered from the pole divisor at a given radius. -/
def conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered
    (D : conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data)
    (radius : ℕ) : ℕ :=
  ∑ i : Fin D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count,
    if D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i = radius then
      D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i
    else
      0

/-- Pole-divisor recovery statement: summing at any radius gives the radius fiber, and evaluating
at a separated pole radius recovers exactly that pole's multiplicity. -/
def conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_statement
    (D : conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data) : Prop :=
  (∀ radius,
    conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered D radius =
      Finset.sum
        (Finset.univ.filter fun i =>
          D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i = radius)
        fun i =>
          D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i) ∧
    ∀ i,
      conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered D
          (D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i) =
        D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i

lemma conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_filter_sum
    (D : conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data)
    (radius : ℕ) :
    conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered D radius =
      Finset.sum
        (Finset.univ.filter fun i =>
          D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i = radius)
        fun i =>
          D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i := by
  rw [conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered]
  exact
    (Finset.sum_filter
      (s :=
        (Finset.univ :
          Finset
            (Fin
              D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count)))
      (p := fun i =>
        D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i = radius)
      (f := fun i =>
        D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i)).symm

lemma conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_single_radius
    (D : conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data)
    (i : Fin D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count) :
    conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered D
        (D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i) =
      D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i := by
  rw [conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_recovered]
  calc
    (∑ j : Fin D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count,
        if D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius j =
            D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i then
          D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity j
        else
          0) =
        ∑ j : Fin D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_fiber_count,
          if j = i then
            D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity j
          else
            0 := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      by_cases hji : j = i
      · simp [hji]
      · have hne_radius :
            D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius j ≠
              D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius i := by
          intro hradius
          exact hji
            (D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_radius_injective
              hradius)
        simp [hji, hne_radius]
    _ = D.conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_multiplicity i := by
      simp

/-- Paper label:
`thm:conclusion-single-conductor-torsion-pole-divisor-recovers-histogram`. -/
theorem paper_conclusion_single_conductor_torsion_pole_divisor_recovers_histogram
    (D : conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_data) :
    conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_statement D := by
  refine ⟨?_, ?_⟩
  · exact conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_filter_sum D
  · exact conclusion_single_conductor_torsion_pole_divisor_recovers_histogram_single_radius D

end Omega.Conclusion
