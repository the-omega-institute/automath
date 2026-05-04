import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.Conclusion.CycleLatticeDiscriminantTripleUnity
import Omega.SPG.GraphCycleLatticeDeterminantPrimeSupport

namespace Omega.Conclusion

open Omega.SPG
open GraphCycleLatticeDeterminantPrimeSupportData

/-- Concrete data for comparing the four prime-support avatars in the cycle-lattice UV package:
the Smith determinant support, the torus-kernel primary support, the weighted tree support, and
the theta UV-prefactor support. -/
structure conclusion_cyclelattice_uvprefactor_torus_prime_support_data where
  conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant :
    GraphCycleLatticeDeterminantPrimeSupportData
  conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorNat : ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeNat : ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorNat : ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport :
    Finset ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport : Finset ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport : Finset ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport : Finset ℕ
  conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorNat_eq_determinant :
    conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorNat =
      conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat
  conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeNat_eq_determinant :
    conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeNat =
      conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat
  conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorNat_eq_determinant :
    conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorNat =
      conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat
  conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport_spec :
    ∀ p,
      p ∈ conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport ↔
        Nat.Prime p ∧
          p ∣ conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.kernelCardinality
  conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport_spec :
    ∀ p,
      p ∈ conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport ↔
        Nat.Prime p ∧
          p ∣ conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorNat
  conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport_spec :
    ∀ p,
      p ∈ conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport ↔
        Nat.Prime p ∧
          p ∣ conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeNat
  conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport_spec :
    ∀ p,
      p ∈ conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport ↔
        Nat.Prime p ∧
          p ∣ conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorNat

/-- Paper-facing statement: the triple-unity discriminant package is available, and every prime
has the same support status in the torus kernel, Smith determinant, weighted tree complexity, and
UV theta-prefactor denominator square. -/
def conclusion_cyclelattice_uvprefactor_torus_prime_support_statement
    (D : conclusion_cyclelattice_uvprefactor_torus_prime_support_data) : Prop :=
  conclusion_cyclelattice_discriminant_triple_unity_statement ∧
    ∀ p : ℕ,
      Nat.Prime p →
        (p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport ↔
            p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.primeSupport) ∧
          (p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.primeSupport ↔
            p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport) ∧
          (p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport ↔
            p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport) ∧
          (p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport ↔
            p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport)

/-- Paper label: `thm:conclusion-cyclelattice-uvprefactor-torus-prime-support`. -/
theorem paper_conclusion_cyclelattice_uvprefactor_torus_prime_support
    (D : conclusion_cyclelattice_uvprefactor_torus_prime_support_data) :
    conclusion_cyclelattice_uvprefactor_torus_prime_support_statement D := by
  refine ⟨paper_conclusion_cyclelattice_discriminant_triple_unity, ?_⟩
  intro p hp
  have hdet :=
    paper_graph_cycle_lattice_determinant_prime_support
      D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant
  have hkernel :
      D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.kernelCardinality =
        D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat :=
    hdet.1
  have hdetSupport :
      p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.primeSupport ↔
        Nat.Prime p ∧
          p ∣ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat :=
    hdet.2 p
  have htorus :
      p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport ↔
        Nat.Prime p ∧
          p ∣ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat := by
    rw [D.conclusion_cyclelattice_uvprefactor_torus_prime_support_torusKernelPrimarySupport_spec,
      hkernel]
  have hweighted :
      p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport ↔
        Nat.Prime p ∧
          p ∣ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat := by
    rw [D.conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeSupport_spec,
      D.conclusion_cyclelattice_uvprefactor_torus_prime_support_weightedTreeNat_eq_determinant]
  have huv :
      p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport ↔
        Nat.Prime p ∧
          p ∣ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat := by
    rw [D.conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorSupport_spec,
      D.conclusion_cyclelattice_uvprefactor_torus_prime_support_uvPrefactorNat_eq_determinant]
  have htheta :
      p ∈ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport ↔
        Nat.Prime p ∧
          p ∣ D.conclusion_cyclelattice_uvprefactor_torus_prime_support_determinant.determinantNat := by
    rw [D.conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorSupport_spec,
      D.conclusion_cyclelattice_uvprefactor_torus_prime_support_thetaPrefactorNat_eq_determinant]
  exact ⟨htorus.trans hdetSupport.symm, hdetSupport.trans hweighted.symm,
    hweighted.trans huv.symm, huv.trans htheta.symm⟩

end Omega.Conclusion
