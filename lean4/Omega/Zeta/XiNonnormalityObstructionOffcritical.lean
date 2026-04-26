import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete reference-compatible seed data for the off-critical obstruction. The Boolean
`horizonDefect` records whether the normalized horizon update has an off-critical spectral defect;
`detailedBalanceCertificate` records the detailed-balance regime used by downstream exclusions.
Paper label: `prop:xi-nonnormality-obstruction-offcritical`. -/
structure xi_nonnormality_obstruction_offcritical_data where
  referenceCompatibleRealization : Bool
  reflectionSymmetricNormalization : Bool
  horizonDefect : Bool
  detailedBalanceCertificate : Bool

/-- The concrete off-critical zero event is the presence of the horizon spectral defect. -/
def xi_nonnormality_obstruction_offcritical_data.offcriticalZeroEvent
    (D : xi_nonnormality_obstruction_offcritical_data) : Prop :=
  D.horizonDefect = true

/-- In the seed model, being similar-normal is exactly the absence of the horizon defect. -/
def xi_nonnormality_obstruction_offcritical_data.similarNormal
    (D : xi_nonnormality_obstruction_offcritical_data) : Prop :=
  D.horizonDefect = false

/-- Detailed balance excludes off-critical defects in the concrete seed model. -/
def xi_nonnormality_obstruction_offcritical_data.detailedBalanceExclusion
    (D : xi_nonnormality_obstruction_offcritical_data) : Prop :=
  D.detailedBalanceCertificate = true → Not D.offcriticalZeroEvent

/-- Paper label: `prop:xi-nonnormality-obstruction-offcritical`. -/
theorem paper_xi_nonnormality_obstruction_offcritical
    (D : xi_nonnormality_obstruction_offcritical_data) :
    D.offcriticalZeroEvent <-> Not D.similarNormal := by
  cases D.horizonDefect <;>
    simp [xi_nonnormality_obstruction_offcritical_data.offcriticalZeroEvent,
      xi_nonnormality_obstruction_offcritical_data.similarNormal]

end Omega.Zeta
