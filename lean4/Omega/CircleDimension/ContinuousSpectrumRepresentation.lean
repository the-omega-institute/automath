import Omega.CircleDimension.CommutativeVisibleAlgebra

namespace Omega.CircleDimension

open scoped BigOperators

/-- The characteristic-function multiplier for the singleton address `addr`. -/
def visibleAddressCharacteristic {A : Type*} [Fintype A] (addr : VisibleAddressState A) :
    VisibleAddressState A → ℂ :=
  fun x => if x = addr then 1 else 0

/-- Concrete spectral representation of the finite visible algebra by diagonal characteristic
multipliers. -/
def ContinuousSpectrumRepresentation {A : Type*} [Fintype A] (M : Set (VisibleOperator A))
    (proj : VisibleAddressState A → VisibleOperator A) : Prop :=
  (∀ addr, proj addr ∈ M) ∧
    (∀ addr₁ addr₂, OperatorsCommute (proj addr₁) (proj addr₂)) ∧
    (∀ addr, proj addr = diagonalOperator (visibleAddressCharacteristic addr))

lemma sameTimeAddressProjection_eq_characteristicMultiplier {A : Type*} [Fintype A]
    (addr : VisibleAddressState A) :
    sameTimeAddressProjection addr = diagonalOperator (visibleAddressCharacteristic addr) := by
  funext ψ x
  classical
  by_cases h : x = addr
  · subst h
    simp [sameTimeAddressProjection, diagonalOperator, visibleAddressCharacteristic]
  · have hne : ∃ a, x a ≠ addr a := by
      by_contra hcontra
      push_neg at hcontra
      exact h (funext hcontra)
    rcases hne with ⟨a, ha⟩
    have hz : (∏ b, if x b = addr b then (1 : ℂ) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])
    simp [sameTimeAddressProjection, diagonalOperator, visibleAddressCharacteristic, h, hz]

/-- The diagonal visible algebra admits the finite counting-measure spectral model in which each
same-time projection is multiplication by the characteristic function of the corresponding address
singleton.
    thm:cdim-continuous-spectrum-representation -/
theorem paper_circle_dimension_continuous_spectrum_representation (A : Type*) [Fintype A] :
    ContinuousSpectrumRepresentation (visibleVonNeumannAlgebra A) (sameTimeAddressProjection
      (A := A)) := by
  refine ⟨sameTimeAddressProjection_mem_visibleVonNeumannAlgebra, ?_, ?_⟩
  · intro addr₁ addr₂
    exact sameTimeAddressProjection_commute addr₁ addr₂
  · intro addr
    exact sameTimeAddressProjection_eq_characteristicMultiplier addr

/-- Exact paper-label wrapper for the continuous-spectrum representation theorem.
    thm:cdim-continuous-spectrum-representation -/
theorem paper_cdim_continuous_spectrum_representation (A : Type*) [Fintype A] :
    ContinuousSpectrumRepresentation (visibleVonNeumannAlgebra A)
      (sameTimeAddressProjection (A := A)) := by
  simpa using paper_circle_dimension_continuous_spectrum_representation A

end Omega.CircleDimension
