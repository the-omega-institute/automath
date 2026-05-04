import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

theorem paper_xi_foldbin_gauge_constant_arbitrary_order_bernoulli_annihilator {R : ℕ}
    (hR : 1 ≤ R) (lam : Fin R → ℝ) (hden : ∀ r : Fin R, lam r ≠ 1) :
    (let p : ℝ → ℝ := fun z => ∏ r : Fin R, (z - lam r) / (1 - lam r);
      p 1 = 1 ∧ ∀ r : Fin R, p (lam r) = 0) := by
  classical
  have _ : 1 ≤ R := hR
  dsimp
  constructor
  · apply Finset.prod_eq_one
    intro r _hr
    exact div_self (sub_ne_zero.mpr (Ne.symm (hden r)))
  · intro r
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp)

end Omega.Zeta
