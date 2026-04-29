import Omega.POM.DiagonalRateDiagonalLaguerreDeterminant
import Omega.POM.DiagonalRateRefreshCountRenewalLLNCLT
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:pom-diagonal-rate-refresh-count-scgf-laguerre`.
The diagonal rank-one determinant already has the Laguerre closed form, and the refresh-count
renewal package identifies the first two SCGF derivatives with the LLN and CLT constants. -/
theorem paper_pom_diagonal_rate_refresh_count_scgf_laguerre
    {α : Type} [Fintype α] {n : Nat}
    (w : DiagonalRateRefreshWitness α) (κ : ℝ) (t : α → ℝ)
    (hT2 : diagonalRateRefreshCountT2 κ t ≠ 0)
    (kappaC : Complex) (p : Fin n → Complex) :
    (∀ z : Complex,
      pom_diagonal_rate_diagonal_laguerre_determinant_det kappaC p z =
        (pom_diagonal_rate_diagonal_laguerre_determinant_poly kappaC p).eval (kappaC * z) +
          z *
            (Polynomial.derivative (pom_diagonal_rate_diagonal_laguerre_determinant_poly
              kappaC p)).eval (kappaC * z)) ∧
      w.markovRealization ∧
      w.regenerationProperty ∧
      diagonalRateRefreshCountLLNSpeed κ t = 1 / diagonalRateRefreshCountMean κ t ∧
      diagonalRateRefreshCountCLTVariance κ t = diagonalRateRefreshCountPsiSecond κ t := by
  have hLaguerre := paper_pom_diagonal_rate_diagonal_laguerre_determinant (kappa := kappaC) p
  rcases paper_pom_diagonal_rate_refresh_count_renewal_lln_clt (w := w) κ t hT2 with
    ⟨hMarkov, hRegen, _, _, hLLN, _, hCLT⟩
  exact ⟨hLaguerre, hMarkov, hRegen, hLLN, hCLT⟩

end

end Omega.POM
