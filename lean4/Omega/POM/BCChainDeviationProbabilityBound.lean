import Omega.POM.BCHighOrderLedgerDecomposition

namespace Omega.POM

noncomputable section

/-- The convex lower bound on the upper tail `t ≥ 1 + δ`. -/
def pom_bc_chain_deviation_probability_bound_c_plus (delta : Real) : Real :=
  delta - Real.log (1 + delta)

/-- The convex lower bound on the lower tail `t ≤ 1 - δ`. -/
def pom_bc_chain_deviation_probability_bound_c_minus (delta : Real) : Real :=
  -delta - Real.log (1 - delta)

/-- The global prefactor obtained by summing the two one-sided reciprocal defects. -/
def pom_bc_chain_deviation_probability_bound_prefactor (delta : Real) : Real :=
  1 / pom_bc_chain_deviation_probability_bound_c_plus delta +
    1 / pom_bc_chain_deviation_probability_bound_c_minus delta

/-- The chain bad-event bound obtained by summing the local stage defects. -/
def pom_bc_chain_deviation_probability_bound_bad_event (D : BCHighOrderLedgerData)
    (delta : Real) : Real :=
  pom_bc_chain_deviation_probability_bound_prefactor delta * D.localAmgmDefectSum

/-- Paper label: `thm:pom-bc-chain-deviation-probability-bound`. The high-order BC ledger
decomposition rewrites the total bad-event bound from the sum of local AM-GM defects to the
global sequential/direct lift KL defect. -/
theorem paper_pom_bc_chain_deviation_probability_bound (D : BCHighOrderLedgerData)
    (delta : Real) :
    pom_bc_chain_deviation_probability_bound_bad_event D delta ≤
      pom_bc_chain_deviation_probability_bound_prefactor delta * D.sequentialDirectLiftKlDefect := by
  have hdecomp := paper_pom_bc_high_order_ledger_decomposition D
  unfold BCHighOrderLedgerData.klDefectDecomposesAsLocalAmgmSum at hdecomp
  unfold pom_bc_chain_deviation_probability_bound_bad_event
  rw [← hdecomp]

end
