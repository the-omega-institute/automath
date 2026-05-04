import Omega.Zeta.XiDeltaFlowMomentLadderCommutation

namespace Omega.Zeta

/--
Concrete finite-closure package for the Delta-flow moment ladder.  The field
`xi_delta_flow_nonclosure_support_le_rank_succ` records the rank obstruction supplied by the
moment-ladder commutation interface: a genuinely finite closure has zero independent rank defect,
so at most one support atom can remain.
-/
structure xi_delta_flow_nonclosure_data where
  xi_delta_flow_nonclosure_closureLevel : ℕ
  xi_delta_flow_nonclosure_supportCard : ℕ
  xi_delta_flow_nonclosure_independentRankDefect : ℕ
  xi_delta_flow_nonclosure_support_le_rank_succ :
    xi_delta_flow_nonclosure_supportCard ≤
      xi_delta_flow_nonclosure_independentRankDefect + 1

namespace xi_delta_flow_nonclosure_data

/-- A finite closure has no remaining independent moment-rank defect above the register. -/
def xi_delta_flow_nonclosure_finite_closure (D : xi_delta_flow_nonclosure_data) : Prop :=
  D.xi_delta_flow_nonclosure_independentRankDefect = 0

/-- The single-atom degeneration condition, expressed as support cardinality at most one. -/
def xi_delta_flow_nonclosure_single_atom_degeneration
    (D : xi_delta_flow_nonclosure_data) : Prop :=
  D.xi_delta_flow_nonclosure_supportCard ≤ 1

/-- The nonclosure criterion: finite closure forces single-atom degeneration. -/
def xi_delta_flow_nonclosure_holds (D : xi_delta_flow_nonclosure_data) : Prop :=
  D.xi_delta_flow_nonclosure_finite_closure →
    D.xi_delta_flow_nonclosure_single_atom_degeneration

end xi_delta_flow_nonclosure_data

/-- Paper label: `prop:xi-delta-flow-nonclosure`. -/
theorem paper_xi_delta_flow_nonclosure (D : xi_delta_flow_nonclosure_data) :
    D.xi_delta_flow_nonclosure_holds := by
  intro hclosure
  dsimp [xi_delta_flow_nonclosure_data.xi_delta_flow_nonclosure_single_atom_degeneration,
    xi_delta_flow_nonclosure_data.xi_delta_flow_nonclosure_finite_closure] at *
  simpa [hclosure] using D.xi_delta_flow_nonclosure_support_le_rank_succ

end Omega.Zeta
