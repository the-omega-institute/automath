import Mathlib.Tactic

namespace Omega.Conclusion

/-- A single residue-slice equation written in multiplicative form. -/
structure ResidueSliceEquation where
  residue : ℚ
  amplitude : ℚ
  orbitParameter : ℚ
  residue_eq : residue = amplitude * orbitParameter

/-- Concrete data for the single-slice orbit / double-slice rigidity package. The first slice
records the product `E * m`; the second slice records the twisted product `E * (τ * m)`. -/
structure ResidueSliceSingleOrbitDoubleSliceRigidityData where
  τ : ℚ
  E : ℚ
  m : ℚ
  hE : E ≠ 0
  hm : m ≠ 0
  baseSliceEquation : ResidueSliceEquation
  twistedSliceEquation : ResidueSliceEquation
  base_amplitude : baseSliceEquation.amplitude = E
  base_orbit : baseSliceEquation.orbitParameter = m
  twisted_amplitude : twistedSliceEquation.amplitude = E
  twisted_orbit : twistedSliceEquation.orbitParameter = τ * m

namespace ResidueSliceSingleOrbitDoubleSliceRigidityData

/-- The residue recorded by the untwisted slice. -/
def baseSlice (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : ℚ :=
  D.baseSliceEquation.residue

/-- The residue recorded by the twisted slice. -/
def twistedSlice (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : ℚ :=
  D.twistedSliceEquation.residue

lemma baseSlice_eq (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) :
    D.baseSlice = D.E * D.m := by
  unfold baseSlice
  rw [D.baseSliceEquation.residue_eq, D.base_amplitude, D.base_orbit]

lemma twistedSlice_eq (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) :
    D.twistedSlice = D.E * (D.τ * D.m) := by
  unfold twistedSlice
  rw [D.twistedSliceEquation.residue_eq, D.twisted_amplitude, D.twisted_orbit]

lemma baseSlice_ne_zero (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : D.baseSlice ≠ 0 := by
  rw [D.baseSlice_eq]
  exact mul_ne_zero D.hE D.hm

/-- Explicit multiplicative reparametrization of the one-slice fiber. -/
def singleSliceOrbitLaw (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : Prop :=
  ∀ u : ℚ, u ≠ 0 → (D.E * u) * (D.m / u) = D.baseSlice

/-- The `τ = 1` degeneration collapses the twisted slice back to the unit slice. -/
def unitSliceLaw (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : Prop :=
  D.τ = 1 → D.twistedSlice = D.baseSlice

/-- Two distinct slices recover the twist ratio, then recover `E` and `m` by back-substitution. -/
def doubleSliceRecoveryLaw (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) : Prop :=
  D.twistedSlice / D.baseSlice = D.τ ∧ D.E = D.baseSlice / D.m ∧ D.m = D.baseSlice / D.E

end ResidueSliceSingleOrbitDoubleSliceRigidityData

open ResidueSliceSingleOrbitDoubleSliceRigidityData

/-- Paper label: `thm:conclusion-residue-slice-single-orbit-double-slice-rigidity`. One slice
has a one-parameter multiplicative orbit of representatives; the `τ = 1` degeneration makes the
two slices coincide; and two slice values recover the twist ratio and then recover `E` and `m`
by back-substitution. -/
theorem paper_conclusion_residue_slice_single_orbit_double_slice_rigidity
    (D : ResidueSliceSingleOrbitDoubleSliceRigidityData) :
    D.singleSliceOrbitLaw ∧ D.unitSliceLaw ∧ D.doubleSliceRecoveryLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [D.baseSlice_eq]
    field_simp [hu]
  · intro hτ
    rw [D.twistedSlice_eq, D.baseSlice_eq, hτ]
    ring
  · refine ⟨?_, ?_, ?_⟩
    · rw [D.twistedSlice_eq, D.baseSlice_eq]
      field_simp [D.hE, D.hm]
    · rw [D.baseSlice_eq]
      field_simp [D.hm]
    · rw [D.baseSlice_eq]
      field_simp [D.hE]

end Omega.Conclusion
