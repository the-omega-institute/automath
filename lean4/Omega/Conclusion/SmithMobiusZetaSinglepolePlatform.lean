import Omega.Conclusion.SmithKernelDirichletEulerRationalLocalFactors
import Omega.Conclusion.SmithLossDivisibilityMobiusAtomization

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-smith-mobius-zeta-singlepole-platform`. -/
theorem paper_conclusion_smith_mobius_zeta_singlepole_platform {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ)
    (D : conclusion_smith_kernel_dirichlet_euler_rational_local_factors_data) :
    conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtomFormula smithValuation ∧
      conclusion_smith_kernel_dirichlet_euler_rational_local_factors_statement D := by
  exact ⟨(paper_conclusion_smith_loss_divisibility_mobius_atomization smithValuation).2,
    paper_conclusion_smith_kernel_dirichlet_euler_rational_local_factors D⟩

end Omega.Conclusion
