import Mathlib

namespace Omega.Conclusion

/-- Concrete rank data for the periodic-fiber Boolean interval certificate. -/
structure conclusion_periodic_fiber_boolean_interval_mobius_data where
  n : ℕ

/-- A blockwise microstate records which of the two endpoint block patterns is chosen. -/
def conclusion_periodic_fiber_boolean_interval_mobius_microstate (n : ℕ) :=
  Fin n → Bool

/-- The microstate obtained by choosing the upper block exactly on `S`. -/
def conclusion_periodic_fiber_boolean_interval_mobius_fromSubset (n : ℕ)
    (S : Finset (Fin n)) :
    conclusion_periodic_fiber_boolean_interval_mobius_microstate n :=
  fun j => decide (j ∈ S)

/-- The subset of blocks on which a microstate chooses the upper endpoint pattern. -/
def conclusion_periodic_fiber_boolean_interval_mobius_toSubset (n : ℕ)
    (ω : conclusion_periodic_fiber_boolean_interval_mobius_microstate n) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => ω j = true

/-- Product order on blockwise endpoint choices. -/
def conclusion_periodic_fiber_boolean_interval_mobius_order {n : ℕ}
    (ω η : conclusion_periodic_fiber_boolean_interval_mobius_microstate n) : Prop :=
  ∀ j, ω j = true → η j = true

/-- Möbius value of a rank-`n` Boolean interval. -/
def conclusion_periodic_fiber_boolean_interval_mobius_value (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n

/-- Concrete Boolean interval statement for the periodic-fiber package. -/
def conclusion_periodic_fiber_boolean_interval_mobius_data.booleanIntervalStatement
    (D : conclusion_periodic_fiber_boolean_interval_mobius_data) : Prop :=
  Function.Bijective (conclusion_periodic_fiber_boolean_interval_mobius_fromSubset D.n) ∧
    (∀ S T : Finset (Fin D.n),
      conclusion_periodic_fiber_boolean_interval_mobius_order
          (conclusion_periodic_fiber_boolean_interval_mobius_fromSubset D.n S)
          (conclusion_periodic_fiber_boolean_interval_mobius_fromSubset D.n T) ↔
        S ⊆ T) ∧
    conclusion_periodic_fiber_boolean_interval_mobius_value D.n = (-1 : ℤ) ^ D.n ∧
      conclusion_periodic_fiber_boolean_interval_mobius_value D.n ≠ 0

/-- Paper label: `prop:conclusion-periodic-fiber-boolean-interval-mobius`. -/
theorem paper_conclusion_periodic_fiber_boolean_interval_mobius
    (D : conclusion_periodic_fiber_boolean_interval_mobius_data) :
    D.booleanIntervalStatement := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · constructor
    · intro S T hST
      ext j
      have hj := congr_fun hST j
      by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
        simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset, hS, hT] at hj ⊢
    · intro ω
      refine ⟨conclusion_periodic_fiber_boolean_interval_mobius_toSubset D.n ω, ?_⟩
      funext j
      by_cases hω : ω j = true
      · simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset,
          conclusion_periodic_fiber_boolean_interval_mobius_toSubset, hω]
      · simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset,
          conclusion_periodic_fiber_boolean_interval_mobius_toSubset, hω]
  · intro S T
    constructor
    · intro hOrder j hjS
      have hjT := hOrder j (by
        simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset, hjS])
      by_contra hjNot
      simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset, hjNot] at hjT
    · intro hSub j hjS
      have hjSmem : j ∈ S := by
        by_contra hjNot
        simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset, hjNot] at hjS
      simp [conclusion_periodic_fiber_boolean_interval_mobius_fromSubset, hSub hjSmem]
  · exact pow_ne_zero D.n (by norm_num : (-1 : ℤ) ≠ 0)

end Omega.Conclusion
