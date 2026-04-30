import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Fourier-diagonal data for a periodized convolution operator. The abstract operator predicates
are connected to the concrete non-`ℓ²` Fourier certificate by `hilbertSchmidt_iff_fourier_l2`;
trace-class and `L²`-kernel exclusions are then supplied by the standard implications to
Hilbert--Schmidt. -/
structure conclusion_periodized_convolution_neither_hs_nor_traceclass_data where
  Operator : Type
  convolution : Operator
  fourierDiagonal : ℤ → ℂ
  Bounded : Operator → Prop
  Normal : Operator → Prop
  HilbertSchmidt : Operator → Prop
  TraceClass : Operator → Prop
  HasL2Kernel : Operator → Prop
  bounded_convolution : Bounded convolution
  normal_convolution : Normal convolution
  fourier_not_l2 : ¬ Summable (fun m : ℤ => ‖fourierDiagonal m‖ ^ 2)
  hilbertSchmidt_iff_fourier_l2 :
    HilbertSchmidt convolution ↔ Summable (fun m : ℤ => ‖fourierDiagonal m‖ ^ 2)
  traceClass_implies_hilbertSchmidt :
    TraceClass convolution → HilbertSchmidt convolution
  l2Kernel_implies_hilbertSchmidt :
    HasL2Kernel convolution → HilbertSchmidt convolution

/-- Paper-facing conclusion for the periodized convolution package. -/
def conclusion_periodized_convolution_neither_hs_nor_traceclass_statement
    (D : conclusion_periodized_convolution_neither_hs_nor_traceclass_data) : Prop :=
  D.Bounded D.convolution ∧
    D.Normal D.convolution ∧
      ¬ D.HilbertSchmidt D.convolution ∧
        ¬ D.TraceClass D.convolution ∧ ¬ D.HasL2Kernel D.convolution

/-- Paper label: `thm:conclusion-periodized-convolution-neither-hs-nor-traceclass`. -/
theorem paper_conclusion_periodized_convolution_neither_hs_nor_traceclass
    (D : conclusion_periodized_convolution_neither_hs_nor_traceclass_data) :
    conclusion_periodized_convolution_neither_hs_nor_traceclass_statement D := by
  have hNotHS : ¬ D.HilbertSchmidt D.convolution := by
    intro hHS
    exact D.fourier_not_l2 (D.hilbertSchmidt_iff_fourier_l2.mp hHS)
  refine ⟨D.bounded_convolution, D.normal_convolution, hNotHS, ?_, ?_⟩
  · intro hTrace
    exact hNotHS (D.traceClass_implies_hilbertSchmidt hTrace)
  · intro hKernel
    exact hNotHS (D.l2Kernel_implies_hilbertSchmidt hKernel)

end Omega.Conclusion
