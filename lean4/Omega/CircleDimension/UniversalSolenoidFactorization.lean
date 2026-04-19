import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete data for factoring a solenoid map through the universal solenoid. The discrete-side
inclusion `A → ℚ` is dualized by `dualize`, producing a compact-side map from the universal
solenoid to the target compact group. The field `dualDiagram` records that this dual map is the
canonical projection, and `dualUniqueness` packages uniqueness from the dual diagram. -/
structure UniversalSolenoidFactorizationData where
  A : Type*
  universalSolenoid : Type*
  targetCompact : Type*
  dualInclusion : A → ℚ
  dualize : (A → ℚ) → universalSolenoid → targetCompact
  canonicalProjection : universalSolenoid → targetCompact
  dualDiagram : dualize dualInclusion = canonicalProjection
  dualUniqueness :
    ∀ f : universalSolenoid → targetCompact,
      f = canonicalProjection → f = dualize dualInclusion

namespace UniversalSolenoidFactorizationData

/-- The universal-solenoid factor map obtained by dualizing the discrete inclusion `A → ℚ`. -/
def factorMap (D : UniversalSolenoidFactorizationData) : D.universalSolenoid → D.targetCompact :=
  D.dualize D.dualInclusion

/-- Existence of the factor map. -/
def factorMapExists (D : UniversalSolenoidFactorizationData) : Prop :=
  ∃ f : D.universalSolenoid → D.targetCompact, f = D.factorMap

/-- The factor map agrees with the canonical projection. -/
def factorsCanonicalProjection (D : UniversalSolenoidFactorizationData) : Prop :=
  D.canonicalProjection = D.factorMap

/-- Uniqueness of the factor map among maps inducing the same dual diagram. -/
def factorMapUnique (D : UniversalSolenoidFactorizationData) : Prop :=
  ∀ f : D.universalSolenoid → D.targetCompact,
    f = D.canonicalProjection → f = D.factorMap

end UniversalSolenoidFactorizationData

/-- Dualizing the inclusion `A → ℚ` produces the universal-solenoid factor map, the resulting
compact-side map is exactly the canonical projection, and uniqueness follows from the same dual
diagram.
    thm:cdim-universal-solenoid-factorization -/
theorem paper_cdim_universal_solenoid_factorization (D : UniversalSolenoidFactorizationData) :
    D.factorMapExists ∧ D.factorsCanonicalProjection ∧ D.factorMapUnique := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.factorMap, rfl⟩
  · simpa [UniversalSolenoidFactorizationData.factorMap,
      UniversalSolenoidFactorizationData.factorsCanonicalProjection] using D.dualDiagram.symm
  · intro f hf
    simpa [UniversalSolenoidFactorizationData.factorMap] using D.dualUniqueness f hf

end Omega.CircleDimension
