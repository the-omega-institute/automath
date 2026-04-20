import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.SPG.GraphEnergyShellLatticeCounting

namespace Omega.SPG

/-- Concrete Smith-normal-form data for the torsion kernel of an integral cycle-lattice quotient.
The determinant is recorded both as the energy-shell discriminant and as the product of invariant
factors, while the prime support is the set of primes dividing that product. -/
structure GraphCycleLatticeDeterminantPrimeSupportData where
  energyData : GraphEnergyShellLatticeCountingData
  determinantNat : ℕ
  kernelCardinality : ℕ
  invariantFactors : List ℕ
  primeSupport : Finset ℕ
  determinantNat_eq_prod : determinantNat = invariantFactors.prod
  kernelCardinality_eq_prod : kernelCardinality = invariantFactors.prod
  determinantCast_eq_weighted :
    (determinantNat : ℝ) =
      energyData.discriminantData.edgeWeightProduct *
        energyData.discriminantData.reciprocalTreePolynomial
  primeSupport_mem_iff :
    ∀ p, p ∈ primeSupport ↔ Nat.Prime p ∧ p ∣ invariantFactors.prod

namespace GraphCycleLatticeDeterminantPrimeSupportData

/-- The kernel cardinality of the torus endomorphism equals the determinant read from the cycle
lattice. -/
def kernelCardinalityEqualsDeterminant
    (D : GraphCycleLatticeDeterminantPrimeSupportData) : Prop :=
  D.kernelCardinality = D.determinantNat

/-- The nontrivial primary pieces of the kernel occur exactly at the primes dividing the
determinant. -/
def primeSupportMatchesDeterminant
    (D : GraphCycleLatticeDeterminantPrimeSupportData) : Prop :=
  ∀ p, p ∈ D.primeSupport ↔ Nat.Prime p ∧ p ∣ D.determinantNat

end GraphCycleLatticeDeterminantPrimeSupportData

open GraphCycleLatticeDeterminantPrimeSupportData

/-- The Smith-normal-form decomposition packages the kernel as a finite quotient of the integer
cycle lattice: its cardinality is the determinant, and its prime support is exactly the
determinant's prime divisor set.
    cor:graph-cycle-lattice-determinant-prime-support -/
theorem paper_graph_cycle_lattice_determinant_prime_support
    (D : GraphCycleLatticeDeterminantPrimeSupportData) :
    D.kernelCardinalityEqualsDeterminant ∧ D.primeSupportMatchesDeterminant := by
  obtain ⟨A, _, _, hWeighted⟩ := paper_graph_energy_shell_lattice_counting D.energyData
  have _hDeterminantWitness : (D.determinantNat : ℝ) = Matrix.det A := by
    calc
      (D.determinantNat : ℝ) =
          D.energyData.discriminantData.edgeWeightProduct *
            D.energyData.discriminantData.reciprocalTreePolynomial :=
        D.determinantCast_eq_weighted
      _ = Matrix.det A := by symm; exact hWeighted
  refine ⟨?_, ?_⟩
  · exact D.kernelCardinality_eq_prod.trans D.determinantNat_eq_prod.symm
  · intro p
    show p ∈ D.primeSupport ↔ Nat.Prime p ∧ p ∣ D.determinantNat
    rw [D.primeSupport_mem_iff p, D.determinantNat_eq_prod]

end Omega.SPG
