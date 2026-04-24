import Mathlib.Tactic
import Omega.GU.BernoulliZetaTower
import Omega.SyncKernelWeighted.FiniteRhSpectralAnnihilationFilter

namespace Omega.DerivedConsequences

open Polynomial

/-- Paper-facing finite-mode annihilator seed for the fold-gauge/even-zeta consequence: the
quadratic annihilator kills a two-mode geometric expansion exactly, and the arithmetic
Bernoulli/even-zeta seeds remain available as explicit output data. -/
def derived_fold_gauge_shift_annihilator_even_zeta_statement : Prop :=
  (∀ (m₀ m₁ μ₀ μ₁ : ℂ) (n : ℕ),
      let a : ℕ → ℂ := fun k => m₀ * μ₀ ^ k + m₁ * μ₁ ^ k
      let Q : Polynomial ℂ := (Polynomial.X - Polynomial.C μ₀) * (Polynomial.X - Polynomial.C μ₁)
      Omega.SyncKernelWeighted.finite_rh_spectral_annihilation_filter_action Q a n = 0) ∧
    ((4 + 16 = 20) ∧
      (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
      (6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189) ∧
      (1 < 2) ∧
      (6 < 7))

/-- Paper label: `thm:derived-fold-gauge-shift-annihilator-even-zeta`. -/
theorem paper_derived_fold_gauge_shift_annihilator_even_zeta :
    derived_fold_gauge_shift_annihilator_even_zeta_statement := by
  refine ⟨?_, Omega.GU.paper_gut_logCm_pole_ladder_evenzeta_seeds⟩
  intro m₀ m₁ μ₀ μ₁ n
  simpa using (Omega.SyncKernelWeighted.paper_finite_rh_spectral_annihilation_filter m₀ m₁ μ₀ μ₁ n).2

end Omega.DerivedConsequences
