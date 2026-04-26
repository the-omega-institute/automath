import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete small-rectangle data for a nonabelian Stokes expansion. The four edge transports
define the rectangle holonomy logarithm, while the BCH quadratic contribution and the cubic Magnus
remainder are recorded explicitly together with the final cubic error bound. -/
structure ConclusionNonabelianStokesSmallRectangleData where
  topTransport : ℝ
  rightTransport : ℝ
  bottomTransport : ℝ
  leftTransport : ℝ
  integratedCurvature : ℝ
  bchQuadratic : ℝ
  magnusCubic : ℝ
  cubicError : ℝ
  hholonomy_expansion :
    topTransport + rightTransport - bottomTransport - leftTransport =
      integratedCurvature + bchQuadratic + magnusCubic
  herror_bound : |bchQuadratic + magnusCubic| ≤ cubicError

namespace ConclusionNonabelianStokesSmallRectangleData

/-- Logarithm of the small-rectangle holonomy, written in additive coordinates. -/
def conclusion_nonabelian_stokes_small_rectangle_holonomyLog
    (D : ConclusionNonabelianStokesSmallRectangleData) : ℝ :=
  D.topTransport + D.rightTransport - D.bottomTransport - D.leftTransport

/-- The local logarithm exists in the chosen chart. -/
def localLogExists (D : ConclusionNonabelianStokesSmallRectangleData) : Prop :=
  ∃ L : ℝ, L = D.conclusion_nonabelian_stokes_small_rectangle_holonomyLog

/-- The logarithm of the holonomy differs from the integrated curvature by at most the recorded
cubic BCH/Magnus error. -/
def curvatureLogErrorBound (D : ConclusionNonabelianStokesSmallRectangleData) : Prop :=
  |D.conclusion_nonabelian_stokes_small_rectangle_holonomyLog - D.integratedCurvature| ≤
    D.cubicError

/-- In the abelian specialization, the BCH and Magnus commutator terms vanish exactly and the
holonomy logarithm equals the integrated curvature. -/
def abelianExactness (D : ConclusionNonabelianStokesSmallRectangleData) : Prop :=
  D.bchQuadratic = 0 →
    D.magnusCubic = 0 →
      D.conclusion_nonabelian_stokes_small_rectangle_holonomyLog = D.integratedCurvature

end ConclusionNonabelianStokesSmallRectangleData

open ConclusionNonabelianStokesSmallRectangleData

/-- Paper label: `thm:conclusion-nonabelian-stokes-small-rectangle`. The packaged local logarithm
exists by definition, the BCH/Magnus expansion gives the curvature comparison up to cubic order,
and in the commutative specialization the commutator terms vanish exactly. -/
theorem paper_conclusion_nonabelian_stokes_small_rectangle
    (D : ConclusionNonabelianStokesSmallRectangleData) :
    D.localLogExists ∧ D.curvatureLogErrorBound ∧ D.abelianExactness := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨D.conclusion_nonabelian_stokes_small_rectangle_holonomyLog, rfl⟩
  · unfold ConclusionNonabelianStokesSmallRectangleData.curvatureLogErrorBound
      conclusion_nonabelian_stokes_small_rectangle_holonomyLog
    have hdiff :
        (D.topTransport + D.rightTransport - D.bottomTransport - D.leftTransport) -
            D.integratedCurvature =
          D.bchQuadratic + D.magnusCubic := by
      linarith [D.hholonomy_expansion]
    rw [hdiff]
    exact D.herror_bound
  · intro hbch hmagnus
    unfold conclusion_nonabelian_stokes_small_rectangle_holonomyLog
    linarith [D.hholonomy_expansion, hbch, hmagnus]

end Omega.Conclusion
