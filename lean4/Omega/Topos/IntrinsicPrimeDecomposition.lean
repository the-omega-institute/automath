namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the prime decomposition of intrinsic visibility and budget.
    thm:intrinsic-prime-decomposition -/
theorem paper_conservative_extension_intrinsic_prime_decomposition
    (evalDecomposes kernelDecomposes quotientDecomposes budgetMultiplies budgetAdds : Prop)
    (hEval : evalDecomposes)
    (hKernel : kernelDecomposes)
    (hQuot : quotientDecomposes)
    (hBudgetMul : budgetMultiplies)
    (hBudgetAdd : budgetAdds) :
    evalDecomposes ∧ kernelDecomposes ∧ quotientDecomposes ∧ budgetMultiplies ∧ budgetAdds := by
  exact ⟨hEval, hKernel, hQuot, hBudgetMul, hBudgetAdd⟩

end Omega.Topos
