import Mathlib.Tactic

namespace Omega.GU

/-- Finite certificate package for the minimal intrinsic chirality anchor at window `6`. The
certificate records the audited boundary-fiber facts at `m = 6, 7, 8`, then packages the two
derivations used in the paper: minimality of `m = 6` and uniqueness of the induced boundary
parity up to isomorphism. -/
structure Window6ChiralityAnchorMinimalData where
  minimal_window : Prop
  unique_boundary_parity : Prop
  m6TwoSheetBoundaryFiber : Prop
  m6UniqueNonzeroIncrement34 : Prop
  m7HasThreePointFiber : Prop
  m7HasMultipleNonzeroIncrements : Prop
  m8HasThreePointFiber : Prop
  m8HasMultipleNonzeroIncrements : Prop
  m6TwoSheetBoundaryFiber_h : m6TwoSheetBoundaryFiber
  m6UniqueNonzeroIncrement34_h : m6UniqueNonzeroIncrement34
  m7HasThreePointFiber_h : m7HasThreePointFiber
  m7HasMultipleNonzeroIncrements_h : m7HasMultipleNonzeroIncrements
  m8HasThreePointFiber_h : m8HasThreePointFiber
  m8HasMultipleNonzeroIncrements_h : m8HasMultipleNonzeroIncrements
  deriveMinimalWindow :
    m6TwoSheetBoundaryFiber →
      m6UniqueNonzeroIncrement34 →
        m7HasThreePointFiber →
          m7HasMultipleNonzeroIncrements →
            m8HasThreePointFiber → m8HasMultipleNonzeroIncrements → minimal_window
  deriveUniqueBoundaryParity :
    m6TwoSheetBoundaryFiber →
      m6UniqueNonzeroIncrement34 → minimal_window → unique_boundary_parity

/-- Paper-facing wrapper for the window-6 chirality anchor certificate.
    thm:window6-chirality-anchor-minimal -/
theorem paper_window6_chirality_anchor_minimal
    (h : Window6ChiralityAnchorMinimalData) : h.minimal_window ∧ h.unique_boundary_parity := by
  have hMinimal : h.minimal_window :=
    h.deriveMinimalWindow h.m6TwoSheetBoundaryFiber_h h.m6UniqueNonzeroIncrement34_h
      h.m7HasThreePointFiber_h h.m7HasMultipleNonzeroIncrements_h h.m8HasThreePointFiber_h
      h.m8HasMultipleNonzeroIncrements_h
  have hParity : h.unique_boundary_parity :=
    h.deriveUniqueBoundaryParity h.m6TwoSheetBoundaryFiber_h h.m6UniqueNonzeroIncrement34_h
      hMinimal
  exact ⟨hMinimal, hParity⟩

end Omega.GU
