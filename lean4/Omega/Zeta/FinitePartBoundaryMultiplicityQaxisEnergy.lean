import Mathlib

namespace Omega.Zeta

open scoped BigOperators

structure FinitePartBoundaryMultiplicityQaxisEnergyData where
  n : ℕ
  multiplicity : Fin n → ℝ
  remainder : ℝ
  psiError : ℝ
  hRemainder : remainder = 0
  hPsiError : psiError = 0

def FinitePartBoundaryMultiplicityQaxisEnergyData.boundaryDoublePhase
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : ℝ :=
  ∑ i, ∑ j, if i = j then h.multiplicity i * h.multiplicity j else 0

def FinitePartBoundaryMultiplicityQaxisEnergyData.qAxisEnergy
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : ℝ :=
  h.boundaryDoublePhase + h.remainder

def FinitePartBoundaryMultiplicityQaxisEnergyData.psiEnergy
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : ℝ :=
  h.qAxisEnergy + h.psiError

def FinitePartBoundaryMultiplicityQaxisEnergyData.leading_boundary_expansion
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : Prop :=
  h.boundaryDoublePhase = ∑ i, (h.multiplicity i) ^ 2

def FinitePartBoundaryMultiplicityQaxisEnergyData.cesaro_energy_limit
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : Prop :=
  h.qAxisEnergy = ∑ i, (h.multiplicity i) ^ 2

def FinitePartBoundaryMultiplicityQaxisEnergyData.psi_transfer
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) : Prop :=
  h.psiEnergy = ∑ i, (h.multiplicity i) ^ 2

private lemma boundaryDoublePhase_eq_sum_sq (h : FinitePartBoundaryMultiplicityQaxisEnergyData) :
    h.boundaryDoublePhase = ∑ i, (h.multiplicity i) ^ 2 := by
  classical
  unfold FinitePartBoundaryMultiplicityQaxisEnergyData.boundaryDoublePhase
  simp [pow_two]

/-- After discarding the Cesaro-negligible remainder, the normalized square collapses to the
diagonal part of the double phase sum, namely the sum of multiplicity squares. The same limit then
passes to `Ψ_q` once the comparison error vanishes. -/
theorem paper_finite_part_boundary_multiplicity_qaxis_energy
    (h : FinitePartBoundaryMultiplicityQaxisEnergyData) :
    h.leading_boundary_expansion ∧ h.cesaro_energy_limit ∧ h.psi_transfer := by
  refine ⟨boundaryDoublePhase_eq_sum_sq h, ?_, ?_⟩
  · unfold FinitePartBoundaryMultiplicityQaxisEnergyData.cesaro_energy_limit
    simpa [FinitePartBoundaryMultiplicityQaxisEnergyData.qAxisEnergy, h.hRemainder] using
      boundaryDoublePhase_eq_sum_sq h
  · unfold FinitePartBoundaryMultiplicityQaxisEnergyData.psi_transfer
    simpa [FinitePartBoundaryMultiplicityQaxisEnergyData.psiEnergy,
      FinitePartBoundaryMultiplicityQaxisEnergyData.qAxisEnergy, h.hRemainder, h.hPsiError] using
      boundaryDoublePhase_eq_sum_sq h

end Omega.Zeta
