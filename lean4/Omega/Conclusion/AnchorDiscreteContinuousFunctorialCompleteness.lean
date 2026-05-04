namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-anchor-discrete-continuous-functorial-completeness`. -/
theorem paper_conclusion_anchor_discrete_continuous_functorial_completeness
    (evaluationIso lagrangeFormula kernelReconstruction discreteContinuousEquiv : Prop)
    (hEval : evaluationIso)
    (hLagrange : evaluationIso -> lagrangeFormula)
    (hKernel : evaluationIso -> kernelReconstruction)
    (hEquiv :
      evaluationIso -> lagrangeFormula -> kernelReconstruction -> discreteContinuousEquiv) :
    discreteContinuousEquiv := by
  exact hEquiv hEval (hLagrange hEval) (hKernel hEval)

end Omega.Conclusion
