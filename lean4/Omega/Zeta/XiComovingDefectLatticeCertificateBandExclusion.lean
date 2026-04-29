import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.AppOffcriticalRadiusCompression
import Omega.Zeta.XiJensenSingleRadiusBandExclusion

namespace Omega.Zeta

/-- The visible-window radius `r_* = ϱ e^{-ε}` used in the comoving lattice certificate. -/
noncomputable def xiComovingDefectVisibleRadius (varrho eps : ℝ) : ℝ :=
  varrho * Real.exp (-eps)

/-- The visible half-window `X(r_*,δ₀)` from the comoving single-center formula. -/
noncomputable def xiComovingDefectVisibleWindow (varrho eps delta0 : ℝ) : ℝ :=
  Real.sqrt
    (((xiComovingDefectVisibleRadius varrho eps) ^ 2 * (1 + delta0) ^ 2 - (1 - delta0) ^ 2) /
      (1 - (xiComovingDefectVisibleRadius varrho eps) ^ 2))

/-- The lattice step `Δ = 2 X(r_*,δ₀)`. -/
noncomputable def xiComovingDefectLatticeStep (varrho eps delta0 : ℝ) : ℝ :=
  2 * xiComovingDefectVisibleWindow varrho eps delta0

/-- Concrete wrapper for the lattice-certificate exclusion law: the visible radius is the expected
`ϱ e^{-ε}` scale, the lattice step is twice the visible half-window, the off-critical Cayley point
stays strictly inside the disk at defect `|δ₀| + 1`, and the existing single-radius Jensen
certificate excludes the band whenever `δ₀ ∈ (0,1/2]`. -/
def xiComovingDefectLatticeCertificateBandExclusionStatement
    (varrho eps delta0 : ℝ) : Prop :=
  xiComovingDefectVisibleRadius varrho eps = varrho * Real.exp (-eps) ∧
    xiComovingDefectLatticeStep varrho eps delta0 = 2 * xiComovingDefectVisibleWindow varrho eps delta0 ∧
    0 ≤ xiComovingDefectVisibleWindow varrho eps delta0 ∧
    appOffcriticalModSq 0 (|delta0| + 1) < 1 ∧
    appOffcriticalBoundaryDepth 0 (|delta0| + 1) =
      4 * (|delta0| + 1) / (|delta0| + 2) ^ 2 ∧
    ((0 < delta0 ∧ delta0 ≤ 1 / 2) → noOffcriticalZeroInBand 1 delta0)

/-- The lattice step is the visible-window step by definition; the off-critical compression
package supplies the Cayley bounds, and the existing single-center Jensen certificate gives the
band exclusion once `δ₀` lies in the visible range.
    thm:xi-comoving-defect-lattice-certificate-band-exclusion -/
theorem paper_xi_comoving_defect_lattice_certificate_band_exclusion
    (varrho eps delta0 : ℝ) : xiComovingDefectLatticeCertificateBandExclusionStatement varrho eps delta0 := by
  refine ⟨rfl, rfl, Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · exact appOffcriticalModSq_lt_one 0 (|delta0| + 1) (by positivity)
  · calc
      appOffcriticalBoundaryDepth 0 (|delta0| + 1) =
          4 * (|delta0| + 1) / ((|delta0| + (1 + 1)) * (|delta0| + (1 + 1))) := by
            simpa [pow_two, add_comm, add_left_comm, add_assoc] using
              appOffcriticalBoundaryDepth_closed_form 0 (|delta0| + 1) (by positivity)
      _ = 4 * (|delta0| + 1) / (|delta0| + 2) ^ 2 := by
        ring
  · intro hdelta
    let rho : ℝ := jensenBandRadius 1 delta0 + 1
    let Dzeta : ℝ := Real.log (rho / jensenBandRadius 1 delta0) - 1
    have hrho : jensenBandRadius 1 delta0 < rho := by
      dsimp [rho]
      linarith
    have hDzeta : Dzeta < Real.log (rho / jensenBandRadius 1 delta0) := by
      dsimp [Dzeta]
      linarith
    exact
      paper_xi_jensen_single_radius_band_exclusion 1 delta0 rho Dzeta
        (by norm_num) hdelta hrho hDzeta

end Omega.Zeta
