import Omega.POM.DiagonalRateSchurConcavity
import Omega.POM.DiagonalRateStrictSchurConcavity

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `thm:pom-diagonal-rate-schur-concavity-tp2`. -/
theorem paper_pom_diagonal_rate_schur_concavity_tp2 {n : ℕ} (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {v w : Fin n → ℝ} (hv : IsProbabilityVector v) (hw : IsProbabilityVector w)
    (hmajor : Majorizes w v) :
    pomDiagonalRate v δ ≥ pomDiagonalRate w δ ∧
      (0 < δ → (∑ i : Fin n, (v i) ^ (2 : ℕ) < ∑ i : Fin n, (w i) ^ (2 : ℕ)) →
        pomDiagonalRate v δ > pomDiagonalRate w δ) := by
  refine ⟨paper_pom_diagonal_rate_schur_concavity δ hδ0 (le_of_lt hδ1) hv hw hmajor, ?_⟩
  intro hδpos hsq
  exact paper_pom_diagonal_rate_strict_schur_concavity δ hδpos hδ1 hv hw hmajor hsq

end Omega.POM
