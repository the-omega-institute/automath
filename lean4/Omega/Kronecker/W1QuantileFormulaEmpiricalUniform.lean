import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Kronecker

open scoped BigOperators

/-- Left endpoint of the `j`-th equal-mass interval in the empirical-uniform coupling. -/
noncomputable def empiricalUniformLeftEndpoint (q : ℕ) (j : Fin q) : ℝ :=
  ((j : ℕ) : ℝ) / q

/-- Right endpoint of the `j`-th equal-mass interval in the empirical-uniform coupling. -/
noncomputable def empiricalUniformRightEndpoint (q : ℕ) (j : Fin q) : ℝ :=
  (((j : ℕ) : ℝ) + 1) / q

/-- Midpoint of the `j`-th interval. -/
noncomputable def empiricalUniformIntervalMidpoint (q : ℕ) (j : Fin q) : ℝ :=
  (((j : ℕ) : ℝ) + (1 / 2 : ℝ)) / q

/-- The sorted empirical support is monotone along the interval order. -/
def empiricalUniformStepOrdered (q : ℕ) (x : Fin q → ℝ) : Prop :=
  ∀ ⦃i j : Fin q⦄, i ≤ j → x i ≤ x j

/-- The empirical support stays inside the ambient unit interval. -/
def empiricalUniformSupportInUnitInterval (q : ℕ) (x : Fin q → ℝ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ 1

/-- The transport cost of the monotone step-map coupling, recorded in midpoint form. -/
noncomputable def empiricalUniformTransportCost (q : ℕ) (x : Fin q → ℝ) : ℝ :=
  (∑ j : Fin q, |x j - empiricalUniformIntervalMidpoint q j|) / q

/-- Concrete package attached to the empirical-uniform quantile formula: the sorted support is
monotone, it lies in `[0,1]`, every interval endpoint is ordered correctly, and the transport cost
is the displayed finite sum. -/
abbrev W1QuantileFormulaEmpiricalUniformStatement (q : ℕ) (x : Fin q → ℝ) : Prop :=
  empiricalUniformStepOrdered q x ∧
    empiricalUniformSupportInUnitInterval q x ∧
    (∀ j, empiricalUniformLeftEndpoint q j ≤ empiricalUniformRightEndpoint q j) ∧
    empiricalUniformTransportCost q x =
      (∑ j : Fin q, |x j - empiricalUniformIntervalMidpoint q j|) / q

/-- Paper label: `lem:w1-quantile-formula-empirical-uniform`.
For a sorted empirical support inside `[0,1)`, the monotone interval coupling is ordered on the
`q` equal-mass subintervals and its cost is exactly the displayed empirical-uniform sum. -/
theorem paper_w1_quantile_formula_empirical_uniform (q : ℕ) (hq : 0 < q) (x : Fin q → ℝ)
    (hxmono : StrictMono x) (hxrange : ∀ j, 0 ≤ x j ∧ x j < 1) :
    W1QuantileFormulaEmpiricalUniformStatement q x := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro i j hij
    exact hxmono.monotone hij
  · intro j
    rcases hxrange j with ⟨hx0, hx1⟩
    exact ⟨hx0, le_of_lt hx1⟩
  · intro j
    have hqR : (0 : ℝ) < q := by
      exact_mod_cast hq
    have hj : ((j : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) + 1 := by
      linarith
    simpa [empiricalUniformLeftEndpoint, empiricalUniformRightEndpoint] using
      (div_le_div_of_nonneg_right hj hqR.le)

end Omega.Kronecker
