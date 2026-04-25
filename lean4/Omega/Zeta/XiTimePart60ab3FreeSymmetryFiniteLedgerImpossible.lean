import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryZ6NoGlobalFreeExtension
import Omega.Folding.KilloPrimeFreedomNonFinitizability

namespace Omega.Zeta

/-- A concrete finite-ledger candidate is indexed only by its register rank `k`: the first
obstruction says the window-`6` fiber partition cannot come from a global free finite-group
extension, and the second says a finite additive ledger of rank `k` cannot faithfully linearize
the first `k + 1` prime directions. -/
def xi_time_part60ab3_free_symmetry_finite_ledger_impossible_statement : Prop :=
  ¬ ∃ k : ℕ,
      Omega.Conclusion.conclusion_window6_boundary_z6_no_global_free_extension_global_free_extension
        ∧
      ¬ Omega.Folding.killoFiniteRegisterLinearizationObstructed k

/-- Paper label: `thm:xi-time-part60ab3-free-symmetry-finite-ledger-impossible`.
The proposed free-symmetry explanation already fails at window `6`, and the finite additive-ledger
linearization is independently ruled out for every finite register rank. Hence no combined
free-symmetry / finite-ledger package can exist. -/
theorem paper_xi_time_part60ab3_free_symmetry_finite_ledger_impossible :
    xi_time_part60ab3_free_symmetry_finite_ledger_impossible_statement := by
  intro h
  rcases h with ⟨k, hfree, hledger⟩
  have hk := (Omega.Folding.paper_killo_prime_freedom_non_finitizability.2) k
  have hfree_impossible :
      False := Omega.Conclusion.paper_conclusion_window6_boundary_z6_no_global_free_extension hfree
  have hledger_impossible : False := hledger hk
  exact hfree_impossible

end Omega.Zeta
