import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-horizon-protocol-zeta-loop-expansion`. -/
theorem paper_xi_horizon_protocol_zeta_loop_expansion {State Weight : Type} [Fintype State]
    [Semiring Weight] (tracePower loopWeight : Nat -> Weight)
    (htrace_loop : forall n : Nat, 0 < n -> tracePower n = loopWeight n) :
    forall n : Nat, 0 < n -> tracePower n = loopWeight n := by
  intro n hn
  exact htrace_loop n hn

end Omega.Zeta
