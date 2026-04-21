import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Folding.BinFoldGaugeM6
import Omega.Folding.Window6
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- At `m = 6`, the number of invariant generators of degree `j` is the number of fold fibers whose
cardinality is at least `j`. The audited histogram has support `{2, 3, 4}`, so the count is a
finite sum over these sizes. -/
def foldbinGaugeInvariantDegreeCountSix (degree : ℕ) : ℕ :=
  (if degree ≤ 2 then Omega.cBinFiberHist 6 2 else 0) +
    (if degree ≤ 3 then Omega.cBinFiberHist 6 3 else 0) +
    (if degree ≤ 4 then Omega.cBinFiberHist 6 4 else 0)

/-- The degree profile of the window-`6` invariant ring, recorded as the exponents of the Hilbert
denominator factors `(1 - t^j)`. -/
def foldbinGaugeHilbertSeriesSix : List (Nat × Nat) :=
  [(1, foldbinGaugeInvariantDegreeCountSix 1), (2, foldbinGaugeInvariantDegreeCountSix 2),
    (3, foldbinGaugeInvariantDegreeCountSix 3), (4, foldbinGaugeInvariantDegreeCountSix 4)]

/-- Paper-facing window-`6` specialization of the foldbin gauge-invariant ring package: the gauge
group decomposes fiberwise, the audited histogram gives the invariant-generator multiplicities in
degrees `1` through `4`, and the factorial product matches the explicit group-order formula.
    thm:foldbin-gauge-invariant-ring -/
theorem paper_foldbin_gauge_invariant_ring :
    Omega.Folding.paper_fold_bin_gauge_decomposition 6 ∧
      foldbinGaugeInvariantDegreeCountSix 1 = 21 ∧
      foldbinGaugeInvariantDegreeCountSix 2 = 21 ∧
      foldbinGaugeInvariantDegreeCountSix 3 = 13 ∧
      foldbinGaugeInvariantDegreeCountSix 4 = 9 ∧
      foldbinGaugeHilbertSeriesSix = [(1, 21), (2, 21), (3, 13), (4, 9)] ∧
      (Nat.factorial 2) ^ 8 * (Nat.factorial 3) ^ 4 * (Nat.factorial 4) ^ 9 =
        2 ^ 8 * 6 ^ 4 * 24 ^ 9 := by
  rcases Omega.Folding.paper_fold_bin_gauge_m6 with ⟨hDecomp, h2, h3, h4, _⟩
  refine ⟨hDecomp, ?_, ?_, ?_, ?_, ?_, Omega.gauge_group_order_factored⟩
  · simp [foldbinGaugeInvariantDegreeCountSix, h2, h3, h4]
  · simp [foldbinGaugeInvariantDegreeCountSix, h2, h3, h4]
  · simp [foldbinGaugeInvariantDegreeCountSix, h3, h4]
  · simp [foldbinGaugeInvariantDegreeCountSix, h4]
  · simp [foldbinGaugeHilbertSeriesSix, foldbinGaugeInvariantDegreeCountSix, h2, h3, h4]

end Omega.OperatorAlgebra
