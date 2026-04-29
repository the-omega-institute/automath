import Omega.CircleDimension.NonnullSectionCriterion

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:unit-circle-complete-phase-readable-iff-fiber`.
This is the unit-circle phase wrapper around the existing circle-dimension nonnull-section
criterion. -/
theorem paper_unit_circle_complete_phase_readable_iff_fiber
    {Addr Cert Section Piece ι : Type}
    (read : Addr → Option Cert) (F : Addr → Set Cert)
    (restrict : ι → Section → Piece) (a : Addr) (locals : ι → Piece)
    (hcompat : ∀ a, (read a).isSome ↔ (F a).Nonempty)
    (hGlue : ∃ s : Section, ∀ i : ι, restrict i s = locals i)
    (hinj : Function.Injective (fun s : Section => fun i : ι => restrict i s)) :
    (read a ≠ none ↔ (F a).Nonempty) ∧
      ∃! s : Section, ∀ i : ι, restrict i s = locals i := by
  exact
    (Omega.CircleDimension.paper_cdim_nonnull_section_criterion
      read F restrict a locals hcompat hGlue hinj).2

end Omega.UnitCirclePhaseArithmetic
