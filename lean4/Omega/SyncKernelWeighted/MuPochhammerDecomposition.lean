import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped ArithmeticFunction.Moebius BigOperators

/-- Finite spectral-factor model for `log ζ_M`. -/
noncomputable def mu_pochhammer_decomposition_log_zeta
    (spectrum : Finset ℂ) (mult : ℂ → ℕ) (z : ℂ) : ℂ :=
  -(Finset.sum spectrum fun eig => (mult eig : ℂ) * Complex.log (1 - eig * z))

/-- Finite Möbius-log truncation of the primitive generating function. -/
noncomputable def mu_pochhammer_decomposition_mobius_log
    (spectrum : Finset ℂ) (mult : ℂ → ℕ) (mobius : ℕ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  Finset.sum (Finset.Icc 1 N) fun k =>
    mobius k / (k : ℂ) * mu_pochhammer_decomposition_log_zeta spectrum mult (z ^ k)

/-- The `μ`-Pochhammer logarithm attached to a single spectral value. -/
noncomputable def mu_pochhammer_decomposition_pochhammer_log
    (eig : ℂ) (mobius : ℕ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  Finset.sum (Finset.Icc 1 N) fun k => mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k)

/-- Paper label: `prop:mu-pochhammer-decomposition`. Finite spectral factorization of `log ζ_M`
may be substituted termwise into the finite Möbius-log expansion, and the spectral sum can then
be exchanged with the Möbius sum to obtain the sum of `μ`-Pochhammer logarithms. -/
theorem paper_mu_pochhammer_decomposition :
    ∀ (spectrum : Finset ℂ) (mult : ℂ → ℕ) (mobius : ℕ → ℂ) (z : ℂ) (N : ℕ),
      mu_pochhammer_decomposition_mobius_log spectrum mult mobius z N =
        -(Finset.sum spectrum fun eig =>
          (mult eig : ℂ) * mu_pochhammer_decomposition_pochhammer_log eig mobius z N) := by
  intro spectrum mult mobius z N
  unfold mu_pochhammer_decomposition_mobius_log mu_pochhammer_decomposition_log_zeta
  have h₁ :
      Finset.sum (Finset.Icc 1 N) (fun k =>
        mobius k / (k : ℂ) *
          (-(Finset.sum spectrum fun eig => (mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) =
        Finset.sum (Finset.Icc 1 N) (fun k =>
          Finset.sum spectrum fun eig =>
            -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  have h₂ :
      Finset.sum (Finset.Icc 1 N) (fun k =>
        Finset.sum spectrum fun eig =>
          -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) =
        Finset.sum spectrum (fun eig =>
          Finset.sum (Finset.Icc 1 N) fun k =>
            -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) := by
    rw [Finset.sum_comm]
  have h₃ :
      Finset.sum spectrum (fun eig =>
        Finset.sum (Finset.Icc 1 N) fun k =>
          -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) =
        Finset.sum spectrum (fun eig =>
          -((mult eig : ℂ) *
            Finset.sum (Finset.Icc 1 N) fun k =>
              mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k))) := by
    apply Finset.sum_congr rfl
    intro eig heig
    have hinner :
        Finset.sum (Finset.Icc 1 N) (fun k =>
          -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) =
          Finset.sum (Finset.Icc 1 N) (fun k =>
            -((mult eig : ℂ) * (mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    calc
      Finset.sum (Finset.Icc 1 N) (fun k =>
        -(mobius k / (k : ℂ) * ((mult eig : ℂ) * Complex.log (1 - eig * z ^ k)))) =
          -(Finset.sum (Finset.Icc 1 N) (fun k =>
            (mult eig : ℂ) * (mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k)))) := by
              rw [hinner, ← Finset.sum_neg_distrib]
      _ = -((mult eig : ℂ) *
          Finset.sum (Finset.Icc 1 N) (fun k =>
            mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k))) := by
              rw [Finset.mul_sum]
  have h₄ :
      Finset.sum spectrum (fun eig =>
        -((mult eig : ℂ) *
          Finset.sum (Finset.Icc 1 N) fun k =>
            mobius k / (k : ℂ) * Complex.log (1 - eig * z ^ k))) =
        -(Finset.sum spectrum fun eig =>
          (mult eig : ℂ) * mu_pochhammer_decomposition_pochhammer_log eig mobius z N) := by
    simp_rw [mu_pochhammer_decomposition_pochhammer_log]
    rw [← Finset.sum_neg_distrib]
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end Omega.SyncKernelWeighted
