import Mathlib

namespace Omega.SyncKernelRealInput

open scoped BigOperators

/-- Closed-walk bookkeeping for the tight-rigidity argument. The walk length decomposes as
`2 * tightEdgeCount` plus a finite sum of nonnegative edge defects. -/
structure real_input_40_arity_charge_density_tight_rigidity_data where
  walkLength : ℕ
  tightEdgeCount : ℕ
  defectSlots : ℕ
  edgeDefect : Fin defectSlots → ℕ
  closedWalkBookkeeping :
    walkLength = 2 * tightEdgeCount + ∑ i : Fin defectSlots, edgeDefect i

namespace real_input_40_arity_charge_density_tight_rigidity_data

/-- Summing the nonnegative defects along a closed walk yields the half-density bound. -/
def closedWalkHalfDensityBound (D : real_input_40_arity_charge_density_tight_rigidity_data) :
    Prop :=
  2 * D.tightEdgeCount ≤ D.walkLength

/-- Equality in the half-density bound is equivalent to every defect summand vanishing. -/
def tightEqualityIffAllEdgesTight (D : real_input_40_arity_charge_density_tight_rigidity_data) :
    Prop :=
  2 * D.tightEdgeCount = D.walkLength ↔ ∀ i : Fin D.defectSlots, D.edgeDefect i = 0

/-- When every edge is tight, the closed walk has even length. -/
def tightWalksHaveEvenLength (D : real_input_40_arity_charge_density_tight_rigidity_data) :
    Prop :=
  (∀ i : Fin D.defectSlots, D.edgeDefect i = 0) → Even D.walkLength

end real_input_40_arity_charge_density_tight_rigidity_data

open real_input_40_arity_charge_density_tight_rigidity_data

/-- Paper label: `prop:real-input-40-arity-charge-density-tight-rigidity`. -/
theorem paper_real_input_40_arity_charge_density_tight_rigidity
    (D : real_input_40_arity_charge_density_tight_rigidity_data) :
    D.closedWalkHalfDensityBound ∧ D.tightEqualityIffAllEdgesTight ∧ D.tightWalksHaveEvenLength := by
  refine ⟨?_, ?_, ?_⟩
  · rw [real_input_40_arity_charge_density_tight_rigidity_data.closedWalkHalfDensityBound,
      D.closedWalkBookkeeping]
    exact Nat.le_add_right _ _
  · constructor
    · intro hEq i
      have hBook : D.walkLength = 2 * D.tightEdgeCount + ∑ j : Fin D.defectSlots, D.edgeDefect j :=
        D.closedWalkBookkeeping
      have hSumZero : ∑ j : Fin D.defectSlots, D.edgeDefect j = 0 := by
        omega
      have hLe :
          D.edgeDefect i ≤ ∑ j : Fin D.defectSlots, D.edgeDefect j := by
        simpa using Finset.single_le_sum
          (fun j _ => Nat.zero_le (D.edgeDefect j))
          (by simp : i ∈ (Finset.univ : Finset (Fin D.defectSlots)))
      rw [hSumZero] at hLe
      exact Nat.eq_zero_of_le_zero hLe
    · intro hAll
      have hSumZero : ∑ i : Fin D.defectSlots, D.edgeDefect i = 0 := by
        simp [hAll]
      have hBook : D.walkLength = 2 * D.tightEdgeCount + ∑ i : Fin D.defectSlots, D.edgeDefect i :=
        D.closedWalkBookkeeping
      omega
  · intro hAll
    have hSumZero : ∑ i : Fin D.defectSlots, D.edgeDefect i = 0 := by
      simp [hAll]
    have hBook : D.walkLength = 2 * D.tightEdgeCount + ∑ i : Fin D.defectSlots, D.edgeDefect i :=
      D.closedWalkBookkeeping
    refine ⟨D.tightEdgeCount, ?_⟩
    omega

end Omega.SyncKernelRealInput
