import Omega.SyncKernelWeighted.AbelMertensAnalyticFamily

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `thm:abel-mertens-universal`.
The universal Abel/Mertens wrapper packages the Witt main term, the Mertens asymptotic for the
primitive partial sums, the finite-part closed form, and analyticity of the finite-part branch. -/
theorem paper_abel_mertens_universal (D : SyncKernelAbelMertensAnalyticFamilyData) :
    D.wittGapMainTerm ∧
      (∀ N : Nat, 1 <= N → D.partialSum N = Real.log N + D.mertensConstant) ∧
      D.finitePart = D.logC + ∑' k : Nat, D.mobiusLogZeta (k + 2) ∧
      D.finitePartAnalytic := by
  have hFamily := paper_sync_kernel_abel_mertens_analytic_family D
  have hIhara := paper_ihara_mertens_constant D.toIharaMertensConstantData
  rcases hFamily with ⟨hwitt, _, hanalytic⟩
  rcases hIhara with ⟨hmertens, hfinite⟩
  exact ⟨hwitt, hmertens, hfinite, hanalytic⟩

end

end Omega.SyncKernelWeighted
