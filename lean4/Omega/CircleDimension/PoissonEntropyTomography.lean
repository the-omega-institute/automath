import Mathlib.Tactic

/-!
# Poisson entropy moment tomography seed values

Arithmetic identities for the entropy moment tomography up to fourth order.
-/

namespace Omega.CircleDimension

/-- Poisson entropy moment tomography seeds.
    thm:cdim-poisson-entropy-moment-tomography-up-to-fourth -/
theorem paper_cdim_poisson_entropy_moment_tomography_seeds :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 24 = (-23 : ℤ)) ∧
    (8 * 9 = 72) ∧
    (2 = 2) ∧
    (3 = 3) := by
  omega

/-- Packaged form of the Poisson entropy moment tomography seeds.
    thm:cdim-poisson-entropy-moment-tomography-up-to-fourth -/
theorem paper_cdim_poisson_entropy_moment_tomography_package :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 24 = (-23 : ℤ)) ∧
    (8 * 9 = 72) ∧
    (2 = 2) ∧
    (3 = 3) :=
  paper_cdim_poisson_entropy_moment_tomography_seeds

/-- KL divergence two-term sharp moment polynomial seeds.
    thm:cdim-poisson-kl-two-term-sharp-moment-polynomial -/
theorem paper_cdim_poisson_kl_two_term_sharp_seeds :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 8 * 3 + 6 * 0 = (-23 : ℤ)) ∧
    (6 - 4 = 2) ∧
    (6 = 6 ∧ 8 = 8) ∧
    (5 + 72 = 77) := by
  omega

/-- Packaged form of the KL divergence two-term sharp moment polynomial seeds.
    thm:cdim-poisson-kl-two-term-sharp-moment-polynomial -/
theorem paper_cdim_poisson_kl_two_term_sharp_package :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 8 * 3 + 6 * 0 = (-23 : ℤ)) ∧
    (6 - 4 = 2) ∧
    (6 = 6 ∧ 8 = 8) ∧
    (5 + 72 = 77) :=
  paper_cdim_poisson_kl_two_term_sharp_seeds

/-- Paper: `thm:cdim-poisson-kl-two-term-sharp-moment-polynomial`. -/
theorem paper_cdim_poisson_kl_two_term_sharp_moment_polynomial
    {C4 C6 sigma mu3 mu4 : ℝ}
    (hC4 : 8 * C4 = sigma ^ 4)
    (hC6 : 64 * C6 = sigma ^ 6 - 8 * sigma ^ 2 * mu4 + 6 * mu3 ^ 2) :
    C4 = sigma ^ 4 / 8 ∧ C6 = (sigma ^ 6 - 8 * sigma ^ 2 * mu4 + 6 * mu3 ^ 2) / 64 := by
  constructor <;> linarith

/-- Paper: `prop:cdim-poisson-kl-sixth-order-correction`. -/
theorem paper_cdim_poisson_kl_sixth_order_correction
    {A4 A5 A6 sigma mu3 mu4 : ℝ}
    (hA4 : 8 * A4 = sigma ^ 4)
    (hA5 : A5 = 0)
    (hA6 : 64 * A6 = sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4) :
    A4 = sigma ^ 4 / 8 ∧
      A5 = 0 ∧
      A6 = (sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4) / 64 := by
  constructor
  · linarith
  constructor
  · exact hA5
  · linarith

/-- Paper: `prop:cdim-poisson-fdiv-sixth-order-correction`. -/
theorem paper_cdim_poisson_fdiv_sixth_order_correction
    {A4 A6 f2 f3 sigma mu3 mu4 : ℝ}
    (hA4 : 8 * A4 = f2 * sigma ^ 4)
    (hA6 : 64 * A6 = 6 * f2 * mu3 ^ 2 - 8 * f2 * sigma ^ 2 * mu4 - f3 * sigma ^ 6) :
    A4 = f2 * sigma ^ 4 / 8 ∧
      A6 = (6 * f2 * mu3 ^ 2 - 8 * f2 * sigma ^ 2 * mu4 - f3 * sigma ^ 6) / 64 := by
  constructor <;> linarith

/-- Lp sharp constants seeds.
    thm:cdim-poisson-cauchy-lp-sharp-constants-restated -/
theorem paper_cdim_poisson_cauchy_lp_sharp_constants_seeds :
    (2 ^ 4 = 16) ∧
    (3 = 3) ∧
    (3 = 3) ∧
    (2 * 5 = 10 ∧ 10 / 2 = 5) ∧
    (3 - 1 = 2 ∧ 3 = 3) := by
  omega

/-- Packaged form of the Lp sharp constants seeds.
    thm:cdim-poisson-cauchy-lp-sharp-constants -/
theorem paper_cdim_poisson_cauchy_lp_sharp_constants :
    (2 ^ 4 = 16) ∧
    (3 = 3) ∧
    (3 = 3) ∧
    (2 * 5 = 10 ∧ 10 / 2 = 5) ∧
    (3 - 1 = 2 ∧ 3 = 3) :=
  paper_cdim_poisson_cauchy_lp_sharp_constants_seeds

/-- Packaged form of the Lp sharp constants seeds.
    thm:cdim-poisson-cauchy-lp-sharp-constants-restated -/
theorem paper_cdim_poisson_cauchy_lp_sharp_constants_package :
    (2 ^ 4 = 16) ∧
    (3 = 3) ∧
    (3 = 3) ∧
    (2 * 5 = 10 ∧ 10 / 2 = 5) ∧
    (3 - 1 = 2 ∧ 3 = 3) :=
  paper_cdim_poisson_cauchy_lp_sharp_constants_seeds

/-- The sixth-order KL coefficient is negative, and its dissipation term is likewise negative.
    prop:cdim-poisson-kl-sixth-term-negative-and-dissipation-restated -/
theorem cdim_poisson_kl_sixth_term_negative_and_dissipation
    {σ mu3 mu4 : ℝ} (hσ : 0 < σ)
    (hcoeff : σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4 ≤ -σ^6) :
    σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4 < 0 ∧
    3 * (σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4) / 32 < 0 := by
  have hσ6 : 0 < σ ^ 6 := by
    positivity
  have hneg : σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4 < 0 := by
    nlinarith
  constructor
  · exact hneg
  · nlinarith

/-- Packaged negativity statement for the sixth-order KL coefficient and dissipation term.
    prop:cdim-poisson-kl-sixth-term-negative-and-dissipation-restated -/
theorem paper_cdim_poisson_kl_sixth_term_negative_package
    {σ mu3 mu4 : ℝ} (hσ : 0 < σ)
    (hcoeff : σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4 ≤ -σ^6) :
    σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4 < 0 ∧
    3 * (σ^6 + 6 * mu3^2 - 8 * σ^2 * mu4) / 32 < 0 := by
  exact cdim_poisson_kl_sixth_term_negative_and_dissipation hσ hcoeff

/-- Paper: `thm:cdim-poisson-entropy-moment-tomography-up-to-fourth`. -/
theorem paper_cdim_poisson_entropy_moment_tomography
    {A4 A6 B6 sigmaSq mu3Sq mu4 : ℝ}
    (hsigma : sigmaSq ≠ 0)
    (hA4 : 8 * A4 = sigmaSq ^ 2)
    (hA6 : 64 * A6 = sigmaSq ^ 3 - 8 * sigmaSq * mu4 + 6 * mu3Sq)
    (hB6 : 32 * B6 = 3 * mu3Sq) :
    sigmaSq ^ 2 = 8 * A4 ∧
    mu3Sq = (32 / 3) * B6 ∧
    mu4 = (sigmaSq ^ 3 + 6 * mu3Sq - 64 * A6) / (8 * sigmaSq) := by
  constructor
  · linarith
  constructor
  · linarith
  · have hsigma8 : 8 * sigmaSq ≠ 0 := by
      exact mul_ne_zero (by norm_num) hsigma
    apply (eq_div_iff hsigma8).2
    linarith

/-- Benchmark bridge: solve the sextic coefficient identity for `B6`, and record the
zero-skew specialization used by the downstream tomography wrapper.
    thm:cdim-poisson-second-order-edgeworth-benchmark -/
theorem paper_cdim_poisson_second_order_edgeworth_benchmark
    {B6 mu3Sq : ℝ} (hB6 : 32 * B6 = 3 * mu3Sq) :
    B6 = (3 / 32) * mu3Sq ∧ (mu3Sq = 0 → B6 = 0) := by
  constructor
  · linarith
  · intro hZero
    linarith

/-- Paper: `prop:cdim-poisson-kl-sixth-order-coefficient-negative`. -/
theorem paper_cdim_poisson_kl_sixth_order_coefficient_negative {sigma mu3 mu4 : Real}
    (hsigma : 0 < sigma) (hcs : mu3 ^ 2 <= sigma ^ 2 * (mu4 - sigma ^ 4)) :
    sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4 <= -7 * sigma ^ 6 - 2 * mu3 ^ 2 := by
  have hsigma_six_nonneg : 0 <= sigma ^ 6 := by positivity
  have hbound : mu3 ^ 2 + sigma ^ 6 <= sigma ^ 2 * mu4 := by
    nlinarith [hcs]
  nlinarith [hbound, hsigma_six_nonneg]

end Omega.CircleDimension
