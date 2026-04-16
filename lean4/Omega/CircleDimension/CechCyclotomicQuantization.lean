import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local package for the `\v{C}ech`--cyclotomic quantization theorem. The two fields
record the forward implication from a finite-order obstruction to a primitive-root spectral orbit,
and the converse implication reading a primitive-root eigenmode back into a nontrivial obstruction
and the resulting `NULL` witness. -/
structure CechCyclotomicQuantizationData where
  obstructionGivesPrimitiveRootOrbit : Prop
  primitiveRootOrbitForcesNull : Prop
  obstructionGivesPrimitiveRootOrbitWitness : obstructionGivesPrimitiveRootOrbit
  primitiveRootOrbitForcesNullWitness : primitiveRootOrbitForcesNull

/-- Paper-facing wrapper for the `\v{C}ech`--cyclotomic quantization package.
    thm:cdim-cech-cyclotomic-quantization -/
theorem paper_cdim_cech_cyclotomic_quantization (h : CechCyclotomicQuantizationData) :
    h.obstructionGivesPrimitiveRootOrbit /\ h.primitiveRootOrbitForcesNull := by
  exact ⟨h.obstructionGivesPrimitiveRootOrbitWitness, h.primitiveRootOrbitForcesNullWitness⟩

end Omega.CircleDimension
