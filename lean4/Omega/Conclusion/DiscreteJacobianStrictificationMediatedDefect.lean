import Omega.POM.BCDiscreteJacobianStrictification

namespace Omega.Conclusion

/-- Conclusion-level wrapper for the discrete Jacobian strictification package.
    thm:conclusion-discrete-jacobian-strictification-mediated-defect -/
theorem paper_conclusion_discrete_jacobian_strictification_mediated_defect
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Omega.POM.liftAlongTwoFiber a b (Omega.POM.strictifiedMiddleLift a b) =
        Omega.POM.directUniformLift a b ∧
      (∀ K : Bool → ℝ, Omega.POM.TwoPointMarkovKernel K →
        Omega.POM.liftAlongTwoFiber a b K = Omega.POM.directUniformLift a b →
          K = Omega.POM.strictifiedMiddleLift a b) ∧
      Omega.POM.klDiv (Omega.POM.sequentialUniformLift a b) (Omega.POM.directUniformLift a b) =
        Omega.POM.klDiv Omega.POM.middleUniformLift (Omega.POM.strictifiedMiddleLift a b) := by
  rcases Omega.POM.paper_pom_bc_discrete_jacobian_strictification a b ha hb with
    ⟨hlift, huniq, hkl, _⟩
  exact ⟨hlift, huniq, hkl⟩

end Omega.Conclusion
