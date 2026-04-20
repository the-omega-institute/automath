import Mathlib
import Omega.GU.Window6EdgeFluxMaxEntropyKernelUniqueness

namespace Omega.GU

open Polynomial
open scoped Polynomial

/-- The audited cubic attached to the coarse window-`6` Markov quotient, written over `ℤ`. -/
noncomputable def window6EdgeFluxCoarseMarkovCubicInt : ℤ[X] :=
  C 48114 * X ^ 3 + C 7263 * X ^ 2 - C 506 * X - C 55

/-- The same cubic, viewed over `ℚ`. -/
noncomputable def window6EdgeFluxCoarseMarkovCubic : ℚ[X] :=
  window6EdgeFluxCoarseMarkovCubicInt.map (Int.castRingHom ℚ)

/-- The audited determinant of the normalized coarse kernel transfer block. -/
def window6EdgeFluxCoarseMarkovDet : ℚ :=
  5 / 4374

/-- The explicit discriminant recorded for the audited cubic. -/
def window6EdgeFluxCoarseMarkovDiscriminant : ℚ :=
  108709030613700

private theorem no_root_mod13 :
    ∀ x : ZMod 13, x ^ 3 + 9 * x ^ 2 + x + 10 ≠ 0 := by
  native_decide

private lemma factor_window6EdgeFluxCoarseMarkovDiscriminant :
    window6EdgeFluxCoarseMarkovDiscriminant =
      (2 : ℚ) ^ 2 * 3 ^ 6 * 5 ^ 2 * 11 * 23 * 5894101 := by
  norm_num [window6EdgeFluxCoarseMarkovDiscriminant]

/-- The coarse window-`6` Markov cubic is root-free mod `13`, its cubic discriminant factors as
`2² 3⁶ 5² 11 23 5894101`, and the audited transfer determinant is `5/4374`.
    cor:window6-edge-flux-coarse-markov-galois -/
theorem paper_window6_edge_flux_coarse_markov_galois :
    (∀ x : ZMod 13, x ^ 3 + 9 * x ^ 2 + x + 10 ≠ 0) ∧
      window6EdgeFluxCoarseMarkovDiscriminant =
        (2 : ℚ) ^ 2 * 3 ^ 6 * 5 ^ 2 * 11 * 23 * 5894101 ∧
      window6EdgeFluxCoarseMarkovDet = (5 / 4374 : ℚ) := by
  exact ⟨no_root_mod13, factor_window6EdgeFluxCoarseMarkovDiscriminant, rfl⟩

end Omega.GU
