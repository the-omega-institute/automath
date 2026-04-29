import Omega.Zeta.XiOracleCollapseToeplitzPsdFiniteTruncation

namespace Omega.Zeta

/-- Paper label: `cor:xi-oracle-collapse-single-dyadic-truncation`. -/
theorem paper_xi_oracle_collapse_single_dyadic_truncation
    (D : XiOracleCollapseToeplitzPsdData) :
    ∃ Nbullet N0, N0 ≤ Nbullet ∧ D.finiteTruncationEquivalent N0 ∧
      ∀ ell theta N, ∃ W, D.congruenceWitness N0 ell theta N W := by
  obtain ⟨N0, _hbound, hfinite, hwitness⟩ :=
    paper_xi_oracle_collapse_toeplitz_psd_finite_truncation D
  exact ⟨N0, N0, le_rfl, hfinite, hwitness⟩

end Omega.Zeta
