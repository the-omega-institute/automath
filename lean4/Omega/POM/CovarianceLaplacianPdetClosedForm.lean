import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshWeightedCayleyPrufer

namespace Omega.POM

open scoped BigOperators

/-- The weighted tree sum attached to the covariance Laplacian on the complete graph. -/
def covarianceLaplacianTreeWeight {k : ℕ} (q : Fin k → ℚ) : ℚ :=
  (∏ i, q i) / (∑ i, q i) ^ (k - 1)

/-- The pseudodeterminant obtained by multiplying the Cayley-Prüfer tree weight by the size of the
vertex set and the normalizing total-mass factor. -/
def covarianceLaplacianPdet {k : ℕ} (q : Fin k → ℚ) : ℚ :=
  (k : ℚ) * covarianceLaplacianTreeWeight q * (∑ i, q i) ^ (k - 1)

/-- The covariance Laplacian pseudodeterminant closes to the expected weighted complete-graph
formula.  prop:covariance-laplacian-pdet-closed-form -/
theorem paper_covariance_laplacian_pdet_closed_form (k : ℕ) (hk : 2 ≤ k) (q : Fin k → ℚ)
    (hq_pos : ∀ i, 0 < q i) (hq_sum : (∑ i, q i) = 1) :
    covarianceLaplacianPdet q = k * ∏ i, q i := by
  let i0 : Fin k := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hk⟩
  have hsum_pos : 0 < ∑ i, q i := by
    have hle : q i0 ≤ ∑ i, q i := by
      exact Finset.single_le_sum (fun i _ => le_of_lt (hq_pos i)) (by simp [i0])
    exact lt_of_lt_of_le (hq_pos i0) hle
  have hsum_ne : (∑ i, q i) ≠ 0 := by
    exact ne_of_gt hsum_pos
  let D : DiagonalRateRefreshWeightedCayleyPruferData :=
    { State := Fin k
      instFintype := inferInstance
      pi := q
      S := ∑ i, q i
      tau := covarianceLaplacianTreeWeight q
      hS := hsum_ne
      cayleyPruferClosedForm := by
        simp [covarianceLaplacianTreeWeight] }
  have htree := paper_pom_diagonal_rate_refresh_weighted_cayley_prufer D
  have hmul := congrArg (fun x : ℚ => (k : ℚ) * x) htree
  simpa [covarianceLaplacianPdet, covarianceLaplacianTreeWeight, D, hq_sum, mul_assoc] using hmul

end Omega.POM
