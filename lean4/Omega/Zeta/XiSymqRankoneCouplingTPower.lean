import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Concrete data for the symmetric-`q` rank-one coupling product law. Each root evaluation splits
into one explicit factor of `t` times a residual mode factor. -/
structure XiSymqRankoneCouplingTPowerData where
  q : ℕ
  t : ℝ
  xi_symq_rankone_coupling_t_power_modeFactor : Fin (q + 1) → ℝ
  xi_symq_rankone_coupling_t_power_rootEval : Fin (q + 1) → ℝ
  xi_symq_rankone_coupling_t_power_rootEval_eq :
    ∀ i : Fin (q + 1),
      xi_symq_rankone_coupling_t_power_rootEval i =
        t * xi_symq_rankone_coupling_t_power_modeFactor i

namespace XiSymqRankoneCouplingTPowerData

/-- Multiplying the `q + 1` root evaluations extracts exactly one factor of `t` from each root. -/
def rankoneCouplingTPower (D : XiSymqRankoneCouplingTPowerData) : Prop :=
  (∏ i : Fin (D.q + 1), D.xi_symq_rankone_coupling_t_power_rootEval i) =
    D.t ^ (D.q + 1) * ∏ i : Fin (D.q + 1), D.xi_symq_rankone_coupling_t_power_modeFactor i

lemma xi_symq_rankone_coupling_t_power_prod_formula (D : XiSymqRankoneCouplingTPowerData) :
    D.rankoneCouplingTPower := by
  unfold rankoneCouplingTPower
  calc
    (∏ i : Fin (D.q + 1), D.xi_symq_rankone_coupling_t_power_rootEval i) =
        ∏ i : Fin (D.q + 1), (D.t * D.xi_symq_rankone_coupling_t_power_modeFactor i) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact D.xi_symq_rankone_coupling_t_power_rootEval_eq i
    _ =
        (∏ _i : Fin (D.q + 1), D.t) *
          ∏ i : Fin (D.q + 1), D.xi_symq_rankone_coupling_t_power_modeFactor i := by
            rw [Finset.prod_mul_distrib]
    _ = D.t ^ (D.q + 1) * ∏ i : Fin (D.q + 1), D.xi_symq_rankone_coupling_t_power_modeFactor i := by
          simp

end XiSymqRankoneCouplingTPowerData

open XiSymqRankoneCouplingTPowerData

/-- Paper label: `prop:xi-symq-rankone-coupling-t-power`. In the eigenbasis decomposition, every
root evaluation contributes one factor of `t`, so the total product gains `t^(q+1)`. -/
theorem paper_xi_symq_rankone_coupling_t_power (D : XiSymqRankoneCouplingTPowerData) :
    D.rankoneCouplingTPower := by
  exact D.xi_symq_rankone_coupling_t_power_prod_formula

end Omega.Zeta
