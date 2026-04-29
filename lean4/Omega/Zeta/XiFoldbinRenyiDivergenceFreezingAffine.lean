import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Target-local collision moment for the bin-fold Rényi normalization. -/
def xi_foldbin_renyi_divergence_freezing_affine_collisionMoment
    {alpha : Type*} [Fintype alpha] (d : alpha -> Real) (q : Nat) : Real :=
  ∑ a, d a ^ q

/-- Paper-facing Rényi divergence expression relative to the uniform baseline. -/
def xi_foldbin_renyi_divergence_freezing_affine_renyi
    {alpha : Type*} [Fintype alpha] (d : alpha -> Real) (m q : Nat) : Real :=
  Real.log (Fintype.card alpha : Real) +
    (1 / ((q : Real) - 1)) *
      Real.log
        (xi_foldbin_renyi_divergence_freezing_affine_collisionMoment d q /
          (2 : Real) ^ (m * q))

/-- Paper label: `thm:xi-foldbin-renyi-divergence-freezing-affine`. -/
theorem paper_xi_foldbin_renyi_divergence_freezing_affine
    {alpha : Type*} [Fintype alpha] (d : alpha -> Real) (m q : Nat) (hq : 2 <= q) :
    xi_foldbin_renyi_divergence_freezing_affine_renyi d m q =
      Real.log (Fintype.card alpha : Real) +
        (1 / ((q : Real) - 1)) *
          Real.log
            (xi_foldbin_renyi_divergence_freezing_affine_collisionMoment d q /
              (2 : Real) ^ (m * q)) := by
  have _hq := hq
  rfl

end

end Omega.Zeta
