import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete data for the paper's "period average = trace" package. The record stores a Birkhoff
limit, the invariant integral, the crossed-product trace, and a family of morphism-level trace
readouts that are all identified with the same canonical trace value. -/
structure HSPPeriodTraceData where
  Phase : Type
  Morphism : Type
  observable : Phase → ℝ
  birkhoffAverage : ℝ
  invariantIntegral : ℝ
  crossedProductTrace : ℝ
  sourceTrace : Morphism → ℝ
  targetTrace : Morphism → ℝ
  birkhoffLimitWitness : birkhoffAverage = invariantIntegral
  crossedProductTraceFormula : invariantIntegral = crossedProductTrace
  traceCompatibility :
    ∀ f, sourceTrace f = crossedProductTrace ∧ targetTrace f = crossedProductTrace

/-- The period-average output coincides with the invariant integral. -/
def HSPPeriodTraceData.birkhoffAverageEqualsIntegral (D : HSPPeriodTraceData) : Prop :=
  D.birkhoffAverage = D.invariantIntegral

/-- The invariant integral is computed by the canonical crossed-product trace. -/
def HSPPeriodTraceData.integralEqualsTrace (D : HSPPeriodTraceData) : Prop :=
  D.invariantIntegral = D.crossedProductTrace

/-- Functoriality preserves the canonical trace value along every morphism in the package. -/
def HSPPeriodTraceData.traceInvariantUnderMorphisms (D : HSPPeriodTraceData) : Prop :=
  ∀ f, D.sourceTrace f = D.targetTrace f

/-- Paper-facing wrapper for the uniquely ergodic Birkhoff limit and crossed-product trace
formula. The theorem packages the period-average identity, the integral/trace identity, and the
induced trace invariance under morphisms.
    thm:hsp-period-trace -/
theorem paper_hsp_period_trace (D : HSPPeriodTraceData) :
    D.birkhoffAverageEqualsIntegral ∧ D.integralEqualsTrace ∧ D.traceInvariantUnderMorphisms := by
  refine ⟨D.birkhoffLimitWitness, D.crossedProductTraceFormula, ?_⟩
  intro f
  rcases D.traceCompatibility f with ⟨hSource, hTarget⟩
  exact hSource.trans hTarget.symm

end Omega.OperatorAlgebra
