import Mathlib.Data.Fintype.Card
import Omega.GU.Window6EdgeFluxCoarseMarkovGalois
import Omega.GU.Window6GoldenS3C2C6PhaseSource

namespace Omega.GU

/-- Concrete audit-model stand-in for the product Galois group `S₃ × C₂`. -/
abbrev Window6GoldenAuditGaloisGroup :=
  Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)

/-- The squarefree part of the audited coarse-Markov discriminant. -/
def window6EdgeFluxCoarseMarkovSquarefreeDiscriminant : ℚ :=
  11 * 23 * 5894101

/-- The golden quadratic field is `ℚ(√5)`. -/
def window6GoldenFieldRadicand : ℚ :=
  5

/-- The finite audit-model cardinality attached to the product group `S₃ × C₂`. -/
def window6GoldenAuditCoverDegree : ℕ :=
  Fintype.card Window6GoldenAuditGaloisGroup

/-- Concrete package for the audited `12`-sheeted `S₃ × C₂` cover: the discriminant factorization
isolates a quadratic field different from `ℚ(√5)`, and the product audit group has cardinality
`12` while already containing an element of order `6`.
    cor:window6-golden-s3c2-audit-cover-degree12 -/
def window6GoldenS3C2AuditCoverDegree12 : Prop :=
  window6EdgeFluxCoarseMarkovDiscriminant =
      (2 : ℚ) ^ 2 * 3 ^ 6 * 5 ^ 2 * window6EdgeFluxCoarseMarkovSquarefreeDiscriminant ∧
    window6EdgeFluxCoarseMarkovSquarefreeDiscriminant ≠ window6GoldenFieldRadicand ∧
    window6GoldenAuditCoverDegree = 12 ∧
    ∃ g : Window6GoldenAuditGaloisGroup, g ^ 6 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1

/-- Paper label: `cor:window6-golden-s3c2-audit-cover-degree12`. -/
theorem paper_window6_golden_s3c2_audit_cover_degree12 :
    window6GoldenS3C2AuditCoverDegree12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [window6EdgeFluxCoarseMarkovSquarefreeDiscriminant, mul_assoc, mul_left_comm, mul_comm]
      using paper_window6_edge_flux_coarse_markov_galois.2.1
  · norm_num [window6EdgeFluxCoarseMarkovSquarefreeDiscriminant, window6GoldenFieldRadicand]
  · simpa [window6GoldenAuditCoverDegree, Window6GoldenAuditGaloisGroup] using
      (show Fintype.card (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) = 12 by native_decide)
  · exact paper_window6_golden_s3c2_c6_phase_source
