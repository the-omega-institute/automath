import Omega.Zeta.DerivedZGHardcoreFactorization
import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- Paper-facing ZG `ζ`-factorization package: the finite hard-core Euler truncations satisfy the
uniform factorization law, and the Abel/residue/log-density witness supplies the corresponding
half-plane analytic package. -/
def xi_zg_zeta_factorization_statement : Prop :=
  (∀ D : DerivedZGHardcoreFactorizationData, D.hardcoreFactorizationLaw) ∧
    ∀ W : XiZGAbelResidueLogDensityWitness,
      W.abelBoundaryLaw ∧ W.harmonicMainTerm ∧ W.absoluteConvergenceCriticalLine

/-- Paper label: `thm:xi-zg-zeta-factorization`. -/
def paper_xi_zg_zeta_factorization : Prop :=
  xi_zg_zeta_factorization_statement

theorem xi_zg_zeta_factorization_verified : paper_xi_zg_zeta_factorization := by
  dsimp [paper_xi_zg_zeta_factorization, xi_zg_zeta_factorization_statement]
  constructor
  · intro D
    exact paper_derived_zg_hardcore_factorization D
  · intro W
    exact paper_xi_zg_abel_residue_log_density W

end Omega.Zeta
