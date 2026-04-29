import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Zeta.XiSemistableNodalFiberLocalEpsilonFactor
import Omega.Zeta.XiTerminalZmDeltaCa5DiscriminantFactorizationSemistablePrimes
import Omega.Zeta.XiTerminalZmDeltaCa5LocalEpsilonFactorFromNodeSign

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label:
`cor:xi-terminal-zm-delta-ca5-jacobian-odd-rootnumber-product-rigidity`. -/
theorem paper_xi_terminal_zm_delta_ca5_jacobian_odd_rootnumber_product_rigidity
    (w : ℕ → ℤ) («global» w2 w3 : ℤ)
    (hbad : ∀ p, p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes →
      w p = if p = 37 then -1 else 1)
    (hglobal : «global» = (∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes, w p) * w2 * w3) :
    (∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes, w p) = -1 ∧
      «global» = -w2 * w3 := by
  have hprod :
      (∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes, w p) =
        ∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes,
          (if p = 37 then -1 else 1 : ℤ) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    exact hbad p hp
  have hsign :
      (∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes,
          (if p = 37 then -1 else 1 : ℤ)) = -1 := by
    native_decide
  have hodd : (∏ p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes, w p) = -1 := by
    rw [hprod]
    exact hsign
  refine ⟨hodd, ?_⟩
  rw [hglobal, hodd]
  ring

end Omega.Zeta
