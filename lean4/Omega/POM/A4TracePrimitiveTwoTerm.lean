import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the two-term `A₄` trace/primitive-orbit expansion. The fields record
the Perron contribution, the unique negative real subleading mode, the `ρ₄`-controlled remainder,
the Möbius primitive-orbit formula, the divisor-tail estimate obtained from the `d ≥ 2` terms, and
the resulting alternating-sign primitive two-term asymptotic. -/
structure A4TracePrimitiveTwoTermData where
  tracePerronTerm : Prop
  negativeSubleadingEigenvalue : Prop
  rho4ControlledRemainder : Prop
  mobiusPrimitiveOrbitFormula : Prop
  divisorTermsBoundedBySqrtPerron : Prop
  primitiveOrbitTwoTermExpansion : Prop
  alternatingSubleadingSign : Prop
  tracePerronTerm_h : tracePerronTerm
  negativeSubleadingEigenvalue_h : negativeSubleadingEigenvalue
  rho4ControlledRemainder_h : rho4ControlledRemainder
  mobiusPrimitiveOrbitFormula_h : mobiusPrimitiveOrbitFormula
  deriveDivisorTermsBoundedBySqrtPerron :
    tracePerronTerm → rho4ControlledRemainder → mobiusPrimitiveOrbitFormula →
      divisorTermsBoundedBySqrtPerron
  derivePrimitiveOrbitTwoTermExpansion :
    tracePerronTerm → negativeSubleadingEigenvalue → rho4ControlledRemainder →
      mobiusPrimitiveOrbitFormula → divisorTermsBoundedBySqrtPerron →
      primitiveOrbitTwoTermExpansion
  deriveAlternatingSubleadingSign :
    negativeSubleadingEigenvalue → primitiveOrbitTwoTermExpansion →
      alternatingSubleadingSign

/-- Paper-facing wrapper for the `A₄` two-term trace/primitive-orbit expansion: the trace splits
into the Perron term, the unique negative real subleading term, and a `ρ₄`-controlled remainder;
substituting this into the Möbius primitive-orbit formula and bounding all `d ≥ 2` divisors by the
`r₄^(n/2)` barrier yields the primitive two-term expansion with alternating subleading sign.
    prop:pom-a4-trace-primitive-two-term -/
theorem paper_pom_a4_trace_primitive_two_term (D : A4TracePrimitiveTwoTermData) :
    D.tracePerronTerm ∧
      D.negativeSubleadingEigenvalue ∧
      D.rho4ControlledRemainder ∧
      D.mobiusPrimitiveOrbitFormula ∧
      D.divisorTermsBoundedBySqrtPerron ∧
      D.primitiveOrbitTwoTermExpansion ∧
      D.alternatingSubleadingSign := by
  have hDivisor : D.divisorTermsBoundedBySqrtPerron :=
    D.deriveDivisorTermsBoundedBySqrtPerron D.tracePerronTerm_h D.rho4ControlledRemainder_h
      D.mobiusPrimitiveOrbitFormula_h
  have hPrimitive : D.primitiveOrbitTwoTermExpansion :=
    D.derivePrimitiveOrbitTwoTermExpansion D.tracePerronTerm_h
      D.negativeSubleadingEigenvalue_h D.rho4ControlledRemainder_h
      D.mobiusPrimitiveOrbitFormula_h hDivisor
  exact ⟨D.tracePerronTerm_h, D.negativeSubleadingEigenvalue_h, D.rho4ControlledRemainder_h,
    D.mobiusPrimitiveOrbitFormula_h, hDivisor, hPrimitive,
    D.deriveAlternatingSubleadingSign D.negativeSubleadingEigenvalue_h hPrimitive⟩

end Omega.POM
