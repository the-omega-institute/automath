import Mathlib.Data.Nat.Log
import Omega.POM.ProjectionAsPartitionPrimeRegister

namespace Omega.POM

/-- Seed arithmetic package for the path-graph width/depth complement: the extremal propagation
depth is the ceiling logarithm of the path diameter. -/
def POMEqClosureWidthDepthComplementStatement (n r : Nat) : Prop :=
  let depth := Nat.clog r (n - 1)
  n - 1 ≤ r ^ depth ∧ ∀ t : Nat, t < depth → r ^ t < n - 1

/-- The seed path-completion model realizes the width/depth complement exactly at the ceiling-log
depth.
    thm:pom-eq-closure-width-depth-complement -/
theorem paper_pom_eq_closure_width_depth_complement (n r : Nat) (hn : 3 ≤ n) (hr : 2 ≤ r) :
    POMEqClosureWidthDepthComplementStatement n r := by
  dsimp [POMEqClosureWidthDepthComplementStatement]
  have _hn : 0 < n - 1 := by omega
  have hr' : 1 < r := by omega
  refine ⟨Nat.le_pow_clog hr' (n - 1), ?_⟩
  intro t ht
  exact (Nat.lt_clog_iff_pow_lt hr').mp ht

end Omega.POM
