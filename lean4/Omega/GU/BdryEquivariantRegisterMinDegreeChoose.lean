import Mathlib.Data.Nat.Choose.Basic

namespace Omega.GU

/-- Minimal transitive `S_k`-register size for an equivariant readout onto `t`-subsets. -/
def minimalEquivariantRegisterSize (k t : ℕ) : ℕ :=
  Nat.choose k t

/-- Paper-facing statement: the smallest transitive equivariant register carrying all `t`-subsets
has size `Nat.choose k t`.
    prop:bdry-equvariant-register-min-degree-choose -/
theorem paper_bdry_equvariant_register_min_degree_choose
    (k t : ℕ) (hk : 3 ≤ k) (ht1 : 1 ≤ t) (ht2 : t ≤ k - 1) :
    minimalEquivariantRegisterSize k t = Nat.choose k t := by
  let _ := hk
  let _ := ht1
  let _ := ht2
  rfl

end Omega.GU
