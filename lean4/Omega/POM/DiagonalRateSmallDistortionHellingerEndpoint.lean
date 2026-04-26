import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.RenyiHalfHellingerTensorAdditivity

open scoped BigOperators
open intervalIntegral

namespace Omega.POM

/-- One-point optimal-coupling parameter in the endpoint normalization. -/
def pom_diagonal_rate_small_distortion_hellinger_endpoint_u (A : ℝ) : Unit → ℝ :=
  fun _ => A

/-- The corresponding one-point weight whose Hellinger half-sum is `A`. -/
def pom_diagonal_rate_small_distortion_hellinger_endpoint_w (A : ℝ) : Unit → ℝ :=
  fun _ => A ^ (2 : ℕ)

/-- Endpoint Lagrange multiplier in the normalized large-`κ` regime. -/
noncomputable def pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda (A δ : ℝ) : ℝ :=
  (A ^ (2 : ℕ) - 1) / δ

/-- Integrated endpoint rate profile solving `R'_w(δ) = -λ(δ)`. -/
noncomputable def pom_diagonal_rate_small_distortion_hellinger_endpoint_rate (A : ℝ) : ℝ → ℝ :=
  fun δ => (1 - A ^ (2 : ℕ)) * Real.log δ

private lemma pom_diagonal_rate_small_distortion_hellinger_endpoint_hellinger_eq
    {A : ℝ} (hA : 0 < A) :
    pomHellingerHalfSum (pom_diagonal_rate_small_distortion_hellinger_endpoint_w A) = A := by
  unfold pomHellingerHalfSum pom_diagonal_rate_small_distortion_hellinger_endpoint_w
  simp [Real.sqrt_sq_eq_abs, abs_of_pos hA]

private lemma pom_diagonal_rate_small_distortion_hellinger_endpoint_rate_hasDerivAt
    {A δ : ℝ} (hδ : 0 < δ) :
    HasDerivAt
      (pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A)
      (-pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda A δ) δ := by
  have hlog : HasDerivAt (fun x : ℝ => Real.log x) (1 / δ) δ := by
    simpa using Real.hasDerivAt_log hδ.ne'
  have hrate :
      HasDerivAt
        (pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A)
        ((1 - A ^ (2 : ℕ)) * (1 / δ)) δ := by
    simpa [pom_diagonal_rate_small_distortion_hellinger_endpoint_rate] using
      hlog.const_mul (1 - A ^ (2 : ℕ))
  have hvalue :
      (1 - A ^ (2 : ℕ)) * (1 / δ) =
        -pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda A δ := by
    simp [pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda, div_eq_mul_inv]
    ring_nf
  exact hvalue ▸ hrate

/-- Paper label: `thm:pom-diagonal-rate-small-distortion-hellinger-endpoint`. In the one-point
endpoint model, the optimal-coupling coordinate sum is exactly the Hellinger half-sum, the
quadratic sum is its square, the normalized large-`κ` parameter is
`κ = (A_{1/2}(w)^2 - 1) / δ`, and the integrated rate profile
`R_w(δ) = -(A_{1/2}(w)^2 - 1) log δ` satisfies `R'_w(δ) = -λ(δ)`. -/
theorem paper_pom_diagonal_rate_small_distortion_hellinger_endpoint
    (A δ δ₀ δ₁ : ℝ) (hA : 0 < A) (hδ : 0 < δ) (hδ₀ : 0 < δ₀) (hδ₀₁ : δ₀ ≤ δ₁) :
    let w := pom_diagonal_rate_small_distortion_hellinger_endpoint_w A
    let lam := pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda A
    let rateFn := pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A
    pomHellingerHalfSum w = A ∧
      (∑ x, pom_diagonal_rate_small_distortion_hellinger_endpoint_u A x) =
        pomHellingerHalfSum w ∧
      (∑ x, (pom_diagonal_rate_small_distortion_hellinger_endpoint_u A x) ^ (2 : ℕ)) =
        pomHellingerHalfSum w ^ (2 : ℕ) ∧
      lam δ = (pomHellingerHalfSum w ^ (2 : ℕ) - 1) / δ ∧
      HasDerivAt rateFn (-lam δ) δ ∧
      ∫ x in δ₀..δ₁, -lam x = rateFn δ₁ - rateFn δ₀ := by
  dsimp
  have hHellinger :
      pomHellingerHalfSum (pom_diagonal_rate_small_distortion_hellinger_endpoint_w A) = A :=
    pom_diagonal_rate_small_distortion_hellinger_endpoint_hellinger_eq hA
  have hδ₁ : 0 < δ₁ := lt_of_lt_of_le hδ₀ hδ₀₁
  have hderiv :
      HasDerivAt
        (pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A)
        (-pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda A δ) δ :=
    pom_diagonal_rate_small_distortion_hellinger_endpoint_rate_hasDerivAt hδ
  refine ⟨hHellinger, ?_, ?_, ?_, hderiv, ?_⟩
  · simpa [pom_diagonal_rate_small_distortion_hellinger_endpoint_u] using hHellinger.symm
  · rw [hHellinger]
    simp [pom_diagonal_rate_small_distortion_hellinger_endpoint_u]
  · rw [hHellinger]
    rfl
  · calc
      ∫ x in δ₀..δ₁, -pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda A x
          = ∫ x in δ₀..δ₁, (1 - A ^ (2 : ℕ)) * (1 / x) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with x
              intro _
              simp [pom_diagonal_rate_small_distortion_hellinger_endpoint_lambda, div_eq_mul_inv]
              ring
      _ = (1 - A ^ (2 : ℕ)) * ∫ x in δ₀..δ₁, (1 / x) := by
            rw [intervalIntegral.integral_const_mul]
      _ = (1 - A ^ (2 : ℕ)) * Real.log (δ₁ / δ₀) := by
            rw [integral_one_div_of_pos hδ₀ hδ₁]
      _ = pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A δ₁ -
            pom_diagonal_rate_small_distortion_hellinger_endpoint_rate A δ₀ := by
            rw [Real.log_div hδ₁.ne' hδ₀.ne',
              pom_diagonal_rate_small_distortion_hellinger_endpoint_rate,
              pom_diagonal_rate_small_distortion_hellinger_endpoint_rate]
            ring

end Omega.POM
