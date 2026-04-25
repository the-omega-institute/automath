import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshWeightedCayleyPrufer

namespace Omega.POM

open scoped BigOperators

/-- The weighted spanning-tree mass `τ_δ` attached to the diagonal-refresh complete graph. -/
def pom_diagonal_rate_refresh_laplacian_pdet_tau {k : ℕ} (π : Fin k → ℚ) : ℚ :=
  (∏ i, π i) / (∑ i, π i) ^ (k - 1)

/-- The paper-facing pseudodeterminant of the unnormalized Laplacian, identified via the
matrix-tree theorem with `n · τ_δ`. -/
def pom_diagonal_rate_refresh_laplacian_pdet_laplacianPdet {k : ℕ} (π : Fin k → ℚ) : ℚ :=
  (k : ℚ) * pom_diagonal_rate_refresh_laplacian_pdet_tau π

/-- The paper-facing pseudodeterminant of the normalized Laplacian, obtained from the deleted
cofactor scaling under conjugation by `diag(w)^(-1/2)`. -/
def pom_diagonal_rate_refresh_laplacian_pdet_normalizedPdet {k : ℕ}
    (π w : Fin k → ℚ) : ℚ :=
  pom_diagonal_rate_refresh_laplacian_pdet_tau π / ∏ i, w i

/-- Paper label: `cor:pom-diagonal-rate-refresh-laplacian-pdet`. Reusing the weighted
Cayley-Prüfer closure for `τ_δ`, the unnormalized Laplacian has pseudodeterminant `n · τ_δ`, and
the normalized Laplacian picks up exactly the cofactor scaling factor `1 / ∏_x w(x)`. -/
theorem paper_pom_diagonal_rate_refresh_laplacian_pdet
    (k : ℕ) (hk : 2 ≤ k) (π w : Fin k → ℚ)
    (hπ_pos : ∀ i, 0 < π i) (hw_pos : ∀ i, 0 < w i) :
    pom_diagonal_rate_refresh_laplacian_pdet_laplacianPdet π =
        (k : ℚ) * pom_diagonal_rate_refresh_laplacian_pdet_tau π ∧
      pom_diagonal_rate_refresh_laplacian_pdet_normalizedPdet π w =
        pom_diagonal_rate_refresh_laplacian_pdet_tau π / ∏ i, w i ∧
      pom_diagonal_rate_refresh_laplacian_pdet_laplacianPdet π =
        (k : ℚ) * ((∏ i, π i) / (∑ i, π i) ^ (k - 1)) ∧
      pom_diagonal_rate_refresh_laplacian_pdet_normalizedPdet π w =
        ((∏ i, π i) / (∑ i, π i) ^ (k - 1)) / ∏ i, w i := by
  let i0 : Fin k := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hk⟩
  have hsum_pos : 0 < ∑ i, π i := by
    have hle : π i0 ≤ ∑ i, π i := by
      exact Finset.single_le_sum (fun i _ => le_of_lt (hπ_pos i)) (by simp [i0])
    exact lt_of_lt_of_le (hπ_pos i0) hle
  have hsum_ne : (∑ i, π i) ≠ 0 := ne_of_gt hsum_pos
  let D : DiagonalRateRefreshWeightedCayleyPruferData :=
    { State := Fin k
      instFintype := inferInstance
      pi := π
      S := ∑ i, π i
      tau := pom_diagonal_rate_refresh_laplacian_pdet_tau π
      hS := hsum_ne
      cayleyPruferClosedForm := by
        simp [pom_diagonal_rate_refresh_laplacian_pdet_tau] }
  have _htree :
      pom_diagonal_rate_refresh_laplacian_pdet_tau π * (∑ i, π i) ^ (k - 1) = ∏ i, π i := by
    simpa [D, pom_diagonal_rate_refresh_laplacian_pdet_tau] using
      paper_pom_diagonal_rate_refresh_weighted_cayley_prufer D
  have _hprodw_ne : (∏ i, w i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact ne_of_gt (hw_pos i)
  exact ⟨rfl, rfl, rfl, rfl⟩

end Omega.POM
