import Omega.POM.BCDiscreteJacobianStrictification

namespace Omega.Conclusion

/-- Conclusion-level uniqueness form of the discrete Jacobian strictifier chain rule.
    thm:conclusion-discrete-jacobian-strictifier-chain-rule -/
theorem paper_conclusion_discrete_jacobian_strictifier_chain_rule
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (Kcomp : Bool → ℝ)
    (hKcomp : Omega.POM.TwoPointMarkovKernel Kcomp)
    (hcomp : Omega.POM.liftAlongTwoFiber a b Kcomp = Omega.POM.directUniformLift a b) :
    Kcomp = Omega.POM.strictifiedMiddleLift a b := by
  have huniq := (Omega.POM.paper_pom_bc_discrete_jacobian_strictification a b ha hb).2.1
  exact
    huniq Kcomp hKcomp hcomp

end Omega.Conclusion
