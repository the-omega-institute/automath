import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmS3RootRecoveryCoordinateAutomorphisms
import Omega.Zeta.XiTerminalZmStokesLeyangCommonQuadraticResolvent

namespace Omega.DerivedConsequences

/-- Concrete finite-abelian-ledger proxy: the two displayed Lee--Yang Frobenius generators would
have to commute. -/
def derived_leyang_no_finite_abelian_ledger_finite_abelian_ledger : Prop :=
  Omega.Zeta.xiTerminalZmIotaPerm * Omega.Zeta.xiTerminalZmSigmaPerm =
    Omega.Zeta.xiTerminalZmSigmaPerm * Omega.Zeta.xiTerminalZmIotaPerm

/-- The arithmetic splitting fixes the common quadratic resolvent discriminant at `-111`, while
the explicit `S₃` recovery permutations remain noncommuting, so the Lee--Yang branch coordinate
cannot be accounted for by any finite abelian ledger. -/
def derived_leyang_no_finite_abelian_ledger_statement : Prop :=
  Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
    Omega.Zeta.xiTerminalZmGeneratesS3 ∧
    ¬ derived_leyang_no_finite_abelian_ledger_finite_abelian_ledger

/-- Paper label: `prop:derived-leyang-no-finite-abelian-ledger`. -/
theorem paper_derived_leyang_no_finite_abelian_ledger :
    derived_leyang_no_finite_abelian_ledger_statement := by
  have hquadratic :
      Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
    exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent.2.2
  have hs3 :
      Omega.Zeta.xiTerminalZmGeneratesS3 := by
    rcases
        Omega.Zeta.paper_xi_terminal_zm_s3_root_recovery_coordinate_automorphisms
          0 0 0 (-1) (-1) (by norm_num)
          (by norm_num [Omega.Zeta.xiTerminalZmResolventDerivative])
          (by norm_num [Omega.Zeta.xiTerminalZmResolventDerivative])
      with ⟨_, _, _, _, hs3⟩
    exact hs3
  refine ⟨hquadratic, hs3, ?_⟩
  intro hledger
  exact hs3.2.2.2 hledger

end Omega.DerivedConsequences
