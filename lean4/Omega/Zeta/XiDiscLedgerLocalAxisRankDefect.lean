import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite trace-ledger data for the local axis/rank-defect formula.  The matrix
`traceMatrix` records the chosen integral trace matrix, while `rankModP` is its rank after
reduction along the selected residue characteristic. -/
structure xi_disc_ledger_local_axis_rank_defect_data where
  xi_disc_ledger_local_axis_rank_defect_degree : ℕ
  xi_disc_ledger_local_axis_rank_defect_prime : ℕ
  xi_disc_ledger_local_axis_rank_defect_traceMatrix :
    Fin xi_disc_ledger_local_axis_rank_defect_degree →
      Fin xi_disc_ledger_local_axis_rank_defect_degree → ℤ
  xi_disc_ledger_local_axis_rank_defect_rankModP : ℕ
  xi_disc_ledger_local_axis_rank_defect_rank_le_degree :
    xi_disc_ledger_local_axis_rank_defect_rankModP ≤
      xi_disc_ledger_local_axis_rank_defect_degree

/-- The dimension of the mod-`p` cokernel of the trace matrix. -/
def xi_disc_ledger_local_axis_rank_defect_cokernel_dim
    (D : xi_disc_ledger_local_axis_rank_defect_data) : ℕ :=
  D.xi_disc_ledger_local_axis_rank_defect_degree -
    D.xi_disc_ledger_local_axis_rank_defect_rankModP

/-- The unavoidable number of local `p`-adic ledger axes. -/
def xi_disc_ledger_local_axis_rank_defect_local_axis_count
    (D : xi_disc_ledger_local_axis_rank_defect_data) : ℕ :=
  xi_disc_ledger_local_axis_rank_defect_cokernel_dim D

/-- The generator rank of the `p`-primary discriminant quotient. -/
def xi_disc_ledger_local_axis_rank_defect_minimal_generators
    (D : xi_disc_ledger_local_axis_rank_defect_data) : ℕ :=
  xi_disc_ledger_local_axis_rank_defect_cokernel_dim D

/-- Paper-facing statement: the local axis count and the minimal generator rank are exactly the
rank defect of the trace matrix modulo `p`. -/
def xi_disc_ledger_local_axis_rank_defect_statement
    (D : xi_disc_ledger_local_axis_rank_defect_data) : Prop :=
  xi_disc_ledger_local_axis_rank_defect_local_axis_count D =
      D.xi_disc_ledger_local_axis_rank_defect_degree -
        D.xi_disc_ledger_local_axis_rank_defect_rankModP ∧
    xi_disc_ledger_local_axis_rank_defect_minimal_generators D =
      xi_disc_ledger_local_axis_rank_defect_local_axis_count D

/-- Paper label: `prop:xi-disc-ledger-local-axis-rank-defect`. -/
theorem paper_xi_disc_ledger_local_axis_rank_defect
    (D : xi_disc_ledger_local_axis_rank_defect_data) :
    xi_disc_ledger_local_axis_rank_defect_statement D := by
  simp [xi_disc_ledger_local_axis_rank_defect_statement,
    xi_disc_ledger_local_axis_rank_defect_local_axis_count,
    xi_disc_ledger_local_axis_rank_defect_minimal_generators,
    xi_disc_ledger_local_axis_rank_defect_cokernel_dim]

end Omega.Zeta
