import Omega.Zeta.XiComovingDefectLatticeCertificateBandExclusion
import Omega.Zeta.XiDyadicZeroTracking

namespace Omega.Zeta

/-- Concrete wrapper data for the tropical strip/lattice package. The zero-free strip and the
vertical zero lattice are already encoded by the chapter-local band-exclusion and zero-tracking
certificates. -/
structure XiTerminalZmGodelLeyangTropicalStripLatticeData where

namespace XiTerminalZmGodelLeyangTropicalStripLatticeData

/-- The strip exclusion comes from the concrete comoving band-exclusion certificate at
`δ₀ = 1 / 2`. -/
def zero_free_strip (_ : XiTerminalZmGodelLeyangTropicalStripLatticeData) : Prop :=
  noOffcriticalZeroInBand 1 (1 / 2 : ℝ)

/-- The vertical zero lattice is modeled by the explicit dyadic simple-zero tracking statement at
the central ordinate `γ = 0`. -/
def vertical_zero_lattice (_ : XiTerminalZmGodelLeyangTropicalStripLatticeData) : Prop :=
  XiDyadicZeroTrackingStatement 0

end XiTerminalZmGodelLeyangTropicalStripLatticeData

open XiTerminalZmGodelLeyangTropicalStripLatticeData

/-- Paper label: `thm:xi-terminal-zm-godel-leyang-tropical-strip-lattice`. The existing
band-exclusion certificate yields the zero-free strip, and the explicit dyadic zero-tracking
theorem supplies the vertical simple-zero lattice. -/
theorem paper_xi_terminal_zm_godel_leyang_tropical_strip_lattice
    (D : XiTerminalZmGodelLeyangTropicalStripLatticeData) :
    D.zero_free_strip ∧ D.vertical_zero_lattice := by
  have hstrip :=
    paper_xi_comoving_defect_lattice_certificate_band_exclusion 1 0 (1 / 2 : ℝ)
  have hzero : noOffcriticalZeroInBand 1 (1 / 2 : ℝ) := by
    exact hstrip.2.2.2.2.2 ⟨by norm_num, by norm_num⟩
  exact ⟨hzero, paper_xi_dyadic_zero_tracking 0⟩

end Omega.Zeta
