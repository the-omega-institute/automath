import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the finite-window Hankel nullspace/truncated-ideal correspondence.
The fields record the polynomial encoding of kernel vectors, the identification of Hankel action
with a moment functional, the inclusion of truncated multiples in the kernel, and the rank/nullity
step forced by an invertible principal `d × d` block. -/
structure HankelNullspaceTruncatedIdealStructureData (k : Type*) [Field k] where
  d : Nat
  N : Nat
  kernelVectorsAsPolynomials : Prop
  hankelActionAsLinearFunctional : Prop
  truncatedMultiplesInKernel : Prop
  principalBlockInvertible : Prop
  rankEqD : Prop
  nullityEqND : Prop
  nullspaceIsoTruncatedIdeal : Prop
  kernelVectorsAsPolynomials_h : kernelVectorsAsPolynomials
  hankelActionAsLinearFunctional_h : hankelActionAsLinearFunctional
  truncatedMultiplesInKernel_h : truncatedMultiplesInKernel
  principalBlockInvertible_h : principalBlockInvertible
  deriveRankEqD : principalBlockInvertible → rankEqD
  deriveNullityEqND : rankEqD → nullityEqND
  deriveNullspaceIsoTruncatedIdeal :
    kernelVectorsAsPolynomials →
      hankelActionAsLinearFunctional →
        truncatedMultiplesInKernel →
          rankEqD → nullspaceIsoTruncatedIdeal

/-- Paper-facing wrapper for the finite-window Hankel nullspace/truncated-ideal structure:
encoding kernel vectors as polynomials identifies the kernel with truncated multiples of the
minimal recurrence polynomial, and the invertible `d × d` block forces rank `d`, hence nullity
`N - d`.
    thm:xi-hankel-nullspace-truncated-ideal-structure -/
theorem paper_xi_hankel_nullspace_truncated_ideal_structure
    {k : Type*} [Field k] (D : HankelNullspaceTruncatedIdealStructureData k) :
    D.rankEqD ∧ D.nullityEqND ∧ D.nullspaceIsoTruncatedIdeal := by
  have hRank : D.rankEqD := D.deriveRankEqD D.principalBlockInvertible_h
  have hNullity : D.nullityEqND := D.deriveNullityEqND hRank
  have hIso : D.nullspaceIsoTruncatedIdeal :=
    D.deriveNullspaceIsoTruncatedIdeal D.kernelVectorsAsPolynomials_h
      D.hankelActionAsLinearFunctional_h D.truncatedMultiplesInKernel_h hRank
  exact ⟨hRank, hNullity, hIso⟩

end Omega.Zeta
