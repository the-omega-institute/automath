import Omega.Zeta.XiOracleCollapseToeplitzPsdFiniteTruncation

namespace Omega.Zeta

/-- Paper label: `cor:xi-oracle-elimination-two-axes`. -/
theorem paper_xi_oracle_elimination_two_axes (D : XiOracleCollapseToeplitzPsdData)
    (twoCoprimeAudit allMomentAudit : Prop) (hTwoAxes : twoCoprimeAudit -> allMomentAudit) :
    (exists N0, N0 <= 2 * D.uniformBound /\ D.finiteTruncationEquivalent N0 /\
      (forall ell theta N, exists W, D.congruenceWitness N0 ell theta N W)) /\
      (twoCoprimeAudit -> allMomentAudit) := by
  exact ⟨paper_xi_oracle_collapse_toeplitz_psd_finite_truncation D, hTwoAxes⟩

end Omega.Zeta
