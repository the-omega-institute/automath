import Mathlib.Tactic
import Omega.CircleDimension.StokesExactSequenceDictionary

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting
open scoped BigOperators

/-- Boundary clutching data for a framed line bundle on the closed polydisk. In the explicit split
Stokes model this is just the integral winding vector on `T^n`. -/
abbrev FramedLineBundleBoundaryClass (n : ℕ) := Fin n → ℤ

/-- Relative first-Chern classes in the split Stokes model. -/
abbrev RelativeFirstChernClass (n : ℕ) := (Fin 0 → ℤ) × (Fin n → ℤ)

/-- The relative first-Chern class is realized by the Stokes connecting map from boundary
clutching data into relative cohomology. -/
def relativeC1OfFramedLineBundle (n : ℕ) :
    FramedLineBundleBoundaryClass n → RelativeFirstChernClass n :=
  stokesBoundaryInclusion 0 n

/-- Stokes pairing between a boundary connection one-form and a relative first-Chern class. -/
def stokesRelativeC1Pairing (n : ℕ) (A : Fin n → ℤ) (c : RelativeFirstChernClass n) : ℤ :=
  ∑ i, A i * c.2 i

private theorem relativeC1OfFramedLineBundle_surjective (n : ℕ) :
    Function.Surjective (relativeC1OfFramedLineBundle n) := by
  intro c
  rcases c with ⟨x, y⟩
  refine ⟨y, ?_⟩
  apply Prod.ext
  · funext i
    exact Fin.elim0 i
  · rfl

/-- Paper-facing wrapper: framed line bundles on the closed polydisk are classified by their
boundary winding data, the Stokes connecting map identifies that data with the relative
first-Chern class, and the resulting pairing is the boundary-versus-curvature Stokes pairing.
    thm:cdim-stokes-relative-c1-framed-line-bundles -/
theorem paper_cdim_stokes_relative_c1_framed_line_bundles (n : ℕ) (_hn : 1 ≤ n) :
    Function.Bijective (relativeC1OfFramedLineBundle n) ∧
      Set.range (relativeC1OfFramedLineBundle n) = {c | stokesProjection 0 n c = 0} ∧
      (∀ τ, relativeC1OfFramedLineBundle n τ = stokesBoundaryInclusion 0 n τ) ∧
      (∀ A τ,
        stokesRelativeC1Pairing n A (relativeC1OfFramedLineBundle n τ) = ∑ i, A i * τ i) := by
  rcases paper_cdim_stokes_exact_sequence_dictionary 0 n with ⟨hInj, _hSurj, hRange, _hDecomp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by simpa [relativeC1OfFramedLineBundle] using hInj,
      relativeC1OfFramedLineBundle_surjective n⟩
  · simpa [relativeC1OfFramedLineBundle] using hRange
  · intro τ
    rfl
  · intro A τ
    simp [stokesRelativeC1Pairing, relativeC1OfFramedLineBundle, stokesBoundaryInclusion]

end Omega.CircleDimension
