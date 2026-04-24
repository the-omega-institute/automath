import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The one-step ledger residual against the `f`-level exogenous lift. -/
noncomputable def pom_ledger_residual_stokes_increment_residual_f
    {m : ℕ} (π d_f : Fin m → ℝ) : ℝ :=
  ∑ x, π x * (Real.log (d_f x) - Real.log (π x))

/-- The one-step ledger residual against the coarser `h = g ∘ f` exogenous lift. -/
noncomputable def pom_ledger_residual_stokes_increment_residual_h
    {m n : ℕ} (g : Fin m → Fin n) (π : Fin m → ℝ) (τ d_h : Fin n → ℝ) : ℝ :=
  ∑ x, π x * (Real.log (d_h (g x)) - Real.log (τ (g x)))

/-- The conditional KL remainder written on the fine index set after pulling back the conditional
law and the size-biased baseline along the coarse quotient map. -/
noncomputable def pom_ledger_residual_stokes_increment_conditional_kl
    {m : ℕ} (π : Fin m → ℝ)
    (pom_ledger_residual_stokes_increment_cond : Fin m → ℝ)
    (pom_ledger_residual_stokes_increment_sigma : Fin m → ℝ) : ℝ :=
  ∑ x, π x *
    Real.log
      (pom_ledger_residual_stokes_increment_cond x /
        pom_ledger_residual_stokes_increment_sigma x)

/-- Paper label: `thm:pom-ledger-residual-stokes-increment`. In the concrete finite-fiber model,
expanding the two residuals and substituting the conditional and size-biased factorizations turns
the residual increment into the pulled-back conditional KL divergence. -/
theorem paper_pom_ledger_residual_stokes_increment
    {m n : ℕ}
    (g : Fin m → Fin n)
    (π : Fin m → ℝ)
    (τ : Fin n → ℝ)
    (d_f : Fin m → ℝ)
    (d_h : Fin n → ℝ)
    (pom_ledger_residual_stokes_increment_cond : Fin m → ℝ)
    (pom_ledger_residual_stokes_increment_sigma : Fin m → ℝ)
    (hτ_pos : ∀ y, 0 < τ y)
    (hcond_pos : ∀ x, 0 < pom_ledger_residual_stokes_increment_cond x)
    (hd_h_pos : ∀ y, 0 < d_h y)
    (hsigma_pos : ∀ x, 0 < pom_ledger_residual_stokes_increment_sigma x)
    (hπ : ∀ x, π x = τ (g x) * pom_ledger_residual_stokes_increment_cond x)
    (hd : ∀ x, d_f x = d_h (g x) * pom_ledger_residual_stokes_increment_sigma x) :
    pom_ledger_residual_stokes_increment_residual_h g π τ d_h =
      pom_ledger_residual_stokes_increment_residual_f π d_f +
        pom_ledger_residual_stokes_increment_conditional_kl π
          pom_ledger_residual_stokes_increment_cond
          pom_ledger_residual_stokes_increment_sigma := by
  unfold pom_ledger_residual_stokes_increment_residual_h
    pom_ledger_residual_stokes_increment_residual_f
    pom_ledger_residual_stokes_increment_conditional_kl
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hτ_ne : τ (g x) ≠ 0 := ne_of_gt (hτ_pos (g x))
  have hcond_ne : pom_ledger_residual_stokes_increment_cond x ≠ 0 := ne_of_gt (hcond_pos x)
  have hd_h_ne : d_h (g x) ≠ 0 := ne_of_gt (hd_h_pos (g x))
  have hsigma_ne :
      pom_ledger_residual_stokes_increment_sigma x ≠ 0 :=
    ne_of_gt (hsigma_pos x)
  rw [Real.log_div hcond_ne hsigma_ne, hπ x, hd x,
    Real.log_mul hd_h_ne hsigma_ne, Real.log_mul hτ_ne hcond_ne]
  ring

end

end Omega.POM
