import Mathlib
import Omega.POM.DiagonalRateSchurConcavity

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-strict-schur-concavity`. -/
theorem paper_pom_diagonal_rate_strict_schur_concavity {n : ℕ} (δ : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {v w : Fin n → ℝ} (_hv : Omega.POM.IsProbabilityVector v)
    (_hw : Omega.POM.IsProbabilityVector w) (_hmajor : Omega.POM.Majorizes w v)
    (hsq : ∑ i : Fin n, (v i) ^ (2 : ℕ) < ∑ i : Fin n, (w i) ^ (2 : ℕ)) :
    Omega.POM.pomDiagonalRate v δ > Omega.POM.pomDiagonalRate w δ := by
  have hfactor : 0 < δ * (1 - δ) := by
    exact mul_pos hδ0 (sub_pos.mpr hδ1)
  unfold Omega.POM.pomDiagonalRate
  nlinarith

end Omega.POM
