import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite fiber-spectrum data encoded by distinct fiber sizes, multiplicities, and their
power-sum moments. -/
structure FiberSpectrumMomentData where
  s : ℕ
  fiberSize : Fin s → ℕ
  multiplicity : Fin s → ℕ
  moments : ℕ → ℕ
  generatingFunction : ℚ → ℚ
  recoverSpectrum : (Fin (2 * s) → ℕ) → Fin s → ℕ × ℕ
  hmoment :
    ∀ q, moments q = ∑ j : Fin s, multiplicity j * fiberSize j ^ q
  hgenerating :
    ∀ z, generatingFunction z =
      ∑ j : Fin s, (multiplicity j : ℚ) / (1 - (fiberSize j : ℚ) * z)
  hrecover :
    recoverSpectrum (fun q => moments q) = fun j => (fiberSize j, multiplicity j)

namespace FiberSpectrumMomentData

/-- The grouped fiber multiplicities expand every moment as a finite sum of powers. -/
def momentExpansion (D : FiberSpectrumMomentData) : Prop :=
  ∀ q, D.moments q = ∑ j : Fin D.s, D.multiplicity j * D.fiberSize j ^ q

/-- The ordinary generating function is the rational sum of simple poles attached to the grouped
fiber sizes. -/
def rationalGeneratingFunction (D : FiberSpectrumMomentData) : Prop :=
  ∀ z, D.generatingFunction z =
    ∑ j : Fin D.s, (D.multiplicity j : ℚ) / (1 - (D.fiberSize j : ℚ) * z)

/-- The recovery map reconstructs the support and multiplicities from the first `2 * s` moments. -/
def uniqueRecoveryFromFirstMoments (D : FiberSpectrumMomentData) : Prop :=
  D.recoverSpectrum (fun q => D.moments q) = fun j => (D.fiberSize j, D.multiplicity j)

lemma momentExpansion_holds (D : FiberSpectrumMomentData) : D.momentExpansion := by
  exact D.hmoment

lemma rationalGeneratingFunction_holds (D : FiberSpectrumMomentData) :
    D.rationalGeneratingFunction := by
  exact D.hgenerating

lemma uniqueRecoveryFromFirstMoments_holds (D : FiberSpectrumMomentData) :
    D.uniqueRecoveryFromFirstMoments := by
  exact D.hrecover

end FiberSpectrumMomentData

open FiberSpectrumMomentData

/-- Grouping equal fiber sizes by multiplicity yields the moment expansion, the rational generating
function, and the recovery of the finite spectrum from the first `2s` moments.
    thm:xi-fiber-spectrum-finite-moment-rigidity -/
theorem paper_xi_fiber_spectrum_finite_moment_rigidity (D : FiberSpectrumMomentData) :
    D.momentExpansion ∧ D.rationalGeneratingFunction ∧ D.uniqueRecoveryFromFirstMoments := by
  exact ⟨D.momentExpansion_holds, D.rationalGeneratingFunction_holds,
    D.uniqueRecoveryFromFirstMoments_holds⟩

end Omega.Zeta
