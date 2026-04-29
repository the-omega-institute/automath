import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FiberBiasedPosteriorPoissonBinomial

open scoped BigOperators

namespace Omega.POM

open FiberBiasedPosteriorPoissonBinomialData

noncomputable section

/-- Paper label: `thm:pom-fiber-rewrite-realroot-ulc`.
The fiber polynomial already factors as a Poisson-binomial PGF. Hence every linear factor has a
real negative root, and the Bernoulli variance bound gives the first Newton/ULC inequality needed
for the coefficient package. -/
theorem paper_pom_fiber_rewrite_realroot_ulc (D : FiberBiasedPosteriorPoissonBinomialData) :
    ∃ p : Fin D.rootCount → ℝ,
      (∀ j, 0 < p j ∧ p j < 1) ∧
      (∀ t : ℝ, D.posteriorPgf t = ∏ j : Fin D.rootCount, (1 - p j + p j * t)) ∧
      (∀ j : Fin D.rootCount, ∃ r : ℝ, r < 0 ∧
        ∀ t : ℝ, (1 - p j + p j * t) = p j * (t - r)) ∧
      D.posteriorVariance ≤ D.posteriorMean := by
  rcases paper_pom_fiber_biased_posterior_poisson_binomial D with ⟨p, hp, hpgf, hmean, hvar⟩
  refine ⟨p, hp, hpgf, ?_, ?_⟩
  · intro j
    refine ⟨-(1 - p j) / p j, ?_, ?_⟩
    · have hpj : 0 < p j := (hp j).1
      have hpj1 : p j < 1 := (hp j).2
      have hnum : -(1 - p j) < 0 := by nlinarith
      exact div_neg_of_neg_of_pos hnum hpj
    · intro t
      have hpj_ne : p j ≠ 0 := (hp j).1.ne'
      field_simp [hpj_ne]
      ring
  · rw [hvar, hmean]
    refine Finset.sum_le_sum ?_
    intro j hj
    have hpj0 : 0 < p j := (hp j).1
    have hpj1 : p j < 1 := (hp j).2
    nlinarith

end

end Omega.POM
