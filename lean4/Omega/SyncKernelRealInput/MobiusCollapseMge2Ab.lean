import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Omega.SyncKernelRealInput.MobiusCollapse

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The `m ≥ 2` remainder of the `(1 - z)` Möbius-log branch after subtracting the `m = 1`
contribution. -/
def mobius_collapse_mge2_ab_one_minus (z : ℂ) : ℂ :=
  mobius_collapse_one_minus z - z

/-- The `m ≥ 2` remainder of the `(1 + z)` Möbius-log branch after subtracting the `m = 1`
contribution. -/
def mobius_collapse_mge2_ab_one_plus (z : ℂ) : ℂ :=
  z - z ^ 2 - mobius_collapse_one_plus z

/-- Concrete statement for the `m ≥ 2` Möbius-collapse package with coefficients `a` and `b`. -/
def mobiusCollapseMge2AbStatement (a b z : ℂ) : Prop :=
  mobius_collapse_mge2_ab_one_minus z = -z - Complex.log (1 - z) ∧
    mobius_collapse_mge2_ab_one_plus z = z - z ^ 2 - Complex.log (1 + z) ∧
    (-a) * mobius_collapse_mge2_ab_one_minus z - b * mobius_collapse_mge2_ab_one_plus z =
      (a - b) * z + b * z ^ 2 + a * Complex.log (1 - z) + b * Complex.log (1 + z)

private lemma mobius_collapse_mge2_ab_one_minus_closed (z : ℂ) (hz : ‖z‖ < 1) :
    mobius_collapse_mge2_ab_one_minus z = -z - Complex.log (1 - z) := by
  rcases paper_mobius_collapse z hz with ⟨hminus, _⟩
  calc
    mobius_collapse_mge2_ab_one_minus z = mobius_collapse_one_minus z - z := by rfl
    _ = -Complex.log (1 - z) - z := by rw [hminus]
    _ = -z - Complex.log (1 - z) := by ring

private lemma mobius_collapse_mge2_ab_one_plus_closed (z : ℂ) :
    mobius_collapse_mge2_ab_one_plus z = z - z ^ 2 - Complex.log (1 + z) := by
  rfl

/-- Paper label: `cor:mobius-collapse-mge2-ab`. The `m ≥ 2` branch formulas come from subtracting
the `m = 1` contribution from the existing Möbius-collapse identities, and the general
`(1 - z)^a (1 + z)^b` expression is then just the corresponding linear combination. -/
theorem paper_mobius_collapse_mge2_ab (a b z : ℂ) (hz : ‖z‖ < 1) :
    mobiusCollapseMge2AbStatement a b z := by
  refine ⟨mobius_collapse_mge2_ab_one_minus_closed z hz,
    mobius_collapse_mge2_ab_one_plus_closed z, ?_⟩
  rw [mobius_collapse_mge2_ab_one_minus_closed z hz, mobius_collapse_mge2_ab_one_plus_closed z]
  ring

end

end Omega.SyncKernelRealInput
