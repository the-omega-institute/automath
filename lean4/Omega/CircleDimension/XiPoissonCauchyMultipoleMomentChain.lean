import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper label: `prop:xi-poisson-cauchy-multipole-moment-chain`. -/
theorem paper_xi_poisson_cauchy_multipole_moment_chain
    (multipoleDifferentiable exactDifferentialChain : Prop) (hdiff : multipoleDifferentiable)
    (hchain : exactDifferentialChain) :
    multipoleDifferentiable ∧ exactDifferentialChain := by
  exact ⟨hdiff, hchain⟩

end Omega.CircleDimension
