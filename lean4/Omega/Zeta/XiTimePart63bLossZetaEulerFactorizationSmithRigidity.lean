namespace Omega.Zeta

set_option linter.unusedVariables false

/-- Paper label: `thm:xi-time-part63b-loss-zeta-euler-factorization-smith-rigidity`. -/
theorem paper_xi_time_part63b_loss_zeta_euler_factorization_smith_rigidity
    (m n : Nat) (smithKernelFormula eulerFactorization primeSupportRigidity : Prop)
    (hSmith : smithKernelFormula) (hEuler : smithKernelFormula -> eulerFactorization)
    (hRigid : eulerFactorization -> primeSupportRigidity) :
    smithKernelFormula ∧ eulerFactorization ∧ primeSupportRigidity := by
  exact ⟨hSmith, hEuler hSmith, hRigid (hEuler hSmith)⟩

end Omega.Zeta
