import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The finite coefficient `c_r = Σ_j w_j λ_j^(2r-1)` appearing in the Stirling translation. -/
def xi_time_part9zbb_finite_stirling_sum_translation_c (m : ℕ) (w lam : Fin m → ℂ)
    (r : ℕ) : ℂ :=
  Finset.univ.sum fun j : Fin m => w j * lam j ^ (2 * r - 1)

/-- Truncated odd formal series written in terms of the aggregated coefficients `c_r`. -/
def xi_time_part9zbb_finite_stirling_sum_translation_formal_odd_trunc (R m : ℕ)
    (κ : ℕ → ℂ) (w lam : Fin m → ℂ) : ℂ :=
  Finset.sum (Finset.range R) fun r =>
    κ (r + 1) * xi_time_part9zbb_finite_stirling_sum_translation_c m w lam (r + 1)

/-- The same truncation expanded scale-by-scale before recombining coefficients. -/
def xi_time_part9zbb_finite_stirling_sum_translation_stirling_trunc (R m : ℕ)
    (κ : ℕ → ℂ) (w lam : Fin m → ℂ) : ℂ :=
  Finset.univ.sum fun j : Fin m =>
    w j * (Finset.sum (Finset.range R) fun r => κ (r + 1) * lam j ^ (2 * (r + 1) - 1))

/-- Finite coefficientwise version of the formal translation from the odd Bernoulli/Stirling series
to a finite sum of Stirling remainders. -/
def xi_time_part9zbb_finite_stirling_sum_translation_statement : Prop :=
  ∀ (R m : ℕ) (κ : ℕ → ℂ) (w lam : Fin m → ℂ),
    xi_time_part9zbb_finite_stirling_sum_translation_formal_odd_trunc R m κ w lam =
      xi_time_part9zbb_finite_stirling_sum_translation_stirling_trunc R m κ w lam

/-- Paper label: `thm:xi-time-part9zbb-finite-stirling-sum-translation`. Expanding `c_r` into the
finite scale sum and commuting the finite `r`- and `j`-sums identifies the truncated odd formal
series with the corresponding truncated finite Stirling combination. -/
theorem paper_xi_time_part9zbb_finite_stirling_sum_translation :
    xi_time_part9zbb_finite_stirling_sum_translation_statement := by
  intro R m κ w lam
  calc
    xi_time_part9zbb_finite_stirling_sum_translation_formal_odd_trunc R m κ w lam
        =
          Finset.sum (Finset.range R) fun r =>
            Finset.univ.sum fun j : Fin m =>
              κ (r + 1) * (w j * lam j ^ (2 * (r + 1) - 1)) := by
              simp [xi_time_part9zbb_finite_stirling_sum_translation_formal_odd_trunc,
                xi_time_part9zbb_finite_stirling_sum_translation_c, Finset.mul_sum,
                mul_left_comm, mul_comm]
    _ =
          Finset.univ.sum fun j : Fin m =>
            Finset.sum (Finset.range R) fun r =>
              κ (r + 1) * (w j * lam j ^ (2 * (r + 1) - 1)) := by
            rw [Finset.sum_comm]
    _ = xi_time_part9zbb_finite_stirling_sum_translation_stirling_trunc R m κ w lam := by
          simp [xi_time_part9zbb_finite_stirling_sum_translation_stirling_trunc, Finset.mul_sum,
            mul_left_comm, mul_comm]

end

end Omega.Zeta
