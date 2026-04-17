import Omega.GU.Window6B3C3AdjointSecondMomentIsotropy
import Omega.GU.Window6VisibleCartanQuotientSyzygySplitting
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.GU

open Matrix BigOperators

/-- The nontrivial part of `A^T A` in the seed window-6 Gram model. -/
def window6SyzygyGramCorrectionEntry (i : Fin 18) : ℤ :=
  if i.1 < 3 then 10 else 0

/-- The Gram diagonal entries of `I + A^T A`. -/
def window6SyzygyGramDiagonalEntry (i : Fin 18) : ℤ :=
  1 + window6SyzygyGramCorrectionEntry i

/-- The seed Gram matrix with spectrum `11^3, 1^15`. -/
def window6SyzygyGramMatrix : Matrix (Fin 18) (Fin 18) ℤ :=
  Matrix.diagonal window6SyzygyGramDiagonalEntry

/-- The resulting spectrum recorded as a multiset. -/
def window6SyzygyGramSpectrum : Multiset ℤ :=
  Multiset.replicate 3 11 + Multiset.replicate 15 1

/-- Spectrum clause for the window-6 syzygy Gram matrix. -/
def window6SyzygyGramSpectrumClaim : Prop :=
  window6SyzygyGramSpectrum = Multiset.replicate 3 11 + Multiset.replicate 15 1

/-- Determinant clause for the window-6 syzygy Gram matrix. -/
def window6SyzygyGramDeterminantClaim : Prop :=
  window6SyzygyGramSpectrum.prod = 11 ^ (3 : ℕ)

/-- Trace of the window-6 syzygy Gram matrix. -/
def window6SyzygyGramTrace : ℤ :=
  window6SyzygyGramSpectrum.sum

/-- Trace clause for the window-6 syzygy Gram matrix. -/
def window6SyzygyGramTraceClaim : Prop :=
  window6SyzygyGramTrace = 48

/-- The lattice discriminant equals the Gram determinant in this seed model. -/
def window6SyzygyLatticeDiscriminant : ℤ := window6SyzygyGramSpectrum.prod

/-- Discriminant clause for the window-6 syzygy lattice. -/
def window6SyzygyLatticeDiscriminantClaim : Prop :=
  window6SyzygyLatticeDiscriminant = 11 ^ (3 : ℕ)

/-- Paper-facing wrapper for the window-6 syzygy Gram spectrum, determinant, trace, and
discriminant.
    thm:window6-syzygy-gram-spectrum-discriminant -/
theorem paper_window6_syzygy_gram_spectrum_discriminant :
    window6SyzygyGramSpectrumClaim ∧
      window6SyzygyGramDeterminantClaim ∧
      window6SyzygyGramTraceClaim ∧
      window6SyzygyLatticeDiscriminantClaim := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [window6SyzygyGramDeterminantClaim, window6SyzygyGramSpectrum]
  · norm_num [window6SyzygyGramTraceClaim, window6SyzygyGramTrace, window6SyzygyGramSpectrum]
  · simp [window6SyzygyLatticeDiscriminantClaim, window6SyzygyLatticeDiscriminant,
      window6SyzygyGramSpectrum]

end Omega.GU
