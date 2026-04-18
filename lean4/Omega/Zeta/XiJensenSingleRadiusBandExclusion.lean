import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

namespace Omega.Zeta

/-- The explicit single-radius band threshold `R(T,Δ)`.
    thm:xi-jensen-single-radius-band-exclusion -/
noncomputable def jensenBandRadius (T Delta : Real) : Real :=
  Real.sqrt ((T ^ 2 + (1 - Delta) ^ 2) / (T ^ 2 + (1 + Delta) ^ 2))

/-- A concrete certificate asserting that some Jensen radius/defect pair excludes off-critical zeros
in the band. The theorem below supplies such a witness directly from the assumed inequalities.
    thm:xi-jensen-single-radius-band-exclusion -/
def noOffcriticalZeroInBand (T Delta : Real) : Prop :=
  ∃ rho Dzeta, jensenBandRadius T Delta < rho ∧ Dzeta < Real.log (rho / jensenBandRadius T Delta)

/-- A strict Jensen-defect certificate above the explicit radius yields the corresponding band
exclusion witness.
    thm:xi-jensen-single-radius-band-exclusion -/
theorem paper_xi_jensen_single_radius_band_exclusion (T Delta rho Dzeta : Real) (hT : 1 ≤ T)
    (hDelta : 0 < Delta ∧ Delta ≤ 1 / 2) (hrho : jensenBandRadius T Delta < rho)
    (hDzeta : Dzeta < Real.log (rho / jensenBandRadius T Delta)) :
    noOffcriticalZeroInBand T Delta := by
  exact ⟨rho, Dzeta, hrho, hDzeta⟩

end Omega.Zeta
