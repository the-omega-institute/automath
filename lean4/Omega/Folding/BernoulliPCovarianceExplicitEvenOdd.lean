import Mathlib.Tactic

namespace Omega.Folding

/-- The `(-p)^(k-1)` coefficient in the Bernoulli-`p` covariance partial fractions. -/
noncomputable def bernoulliPCovarianceB (p : ℝ) : ℝ :=
  -(p ^ 3 * (p ^ 2 - 3 * p + 1) ^ 2) / ((2 * p - 1) * (p + 1) * (1 + p ^ 3))

/-- The even-power coefficient coming from the quadratic denominator. -/
noncomputable def bernoulliPCovarianceE (p : ℝ) : ℝ :=
  p ^ 2 * (1 - p) * (p ^ 5 + 4 * p ^ 4 - 4 * p ^ 3 - 5 * p ^ 2 + 7 * p - 2) /
    ((2 * p - 1) * (1 + p ^ 3) * (p ^ 2 - p + 1))

/-- The odd-power coefficient coming from the quadratic denominator. -/
noncomputable def bernoulliPCovarianceF (p : ℝ) : ℝ :=
  p ^ 2 * (1 - p) ^ 2 * (p ^ 5 - p ^ 4 - 6 * p ^ 3 + 3 * p ^ 2 + 2 * p - 1) /
    ((2 * p - 1) * (1 + p ^ 3) * (p ^ 2 - p + 1))

/-- The `(-p)^k` coefficient in the explicit even/odd closed forms. -/
noncomputable def bernoulliPCovarianceA (p : ℝ) : ℝ :=
  -(p * bernoulliPCovarianceB p)

/-- The odd-index quadratic-mode coefficient. -/
noncomputable def bernoulliPCovarianceC0 (p : ℝ) : ℝ :=
  bernoulliPCovarianceE p

/-- The even-index quadratic-mode coefficient. -/
noncomputable def bernoulliPCovarianceC1 (p : ℝ) : ℝ :=
  bernoulliPCovarianceF p / (p * (1 - p))

/-- The explicit odd branch `c_{2m+1}(p)`. -/
noncomputable def bernoulliPCovarianceOdd (p : ℝ) (m : ℕ) : ℝ :=
  bernoulliPCovarianceA p * (-p) ^ (2 * m) +
    (p * (1 - p)) ^ m * bernoulliPCovarianceC0 p

/-- The explicit even branch `c_{2m+2}(p)`. -/
noncomputable def bernoulliPCovarianceEven (p : ℝ) (m : ℕ) : ℝ :=
  bernoulliPCovarianceA p * (-p) ^ (2 * m + 1) +
    (p * (1 - p)) ^ (m + 1) * bernoulliPCovarianceC1 p

/-- The Jordan-threshold parameter where the pole collision occurs. -/
def bernoulliPCovarianceJordanThreshold (p : ℝ) : Prop :=
  p = 1 / 2

/-- The Bernoulli-`p` covariance splits into explicit odd and even closed forms away from the
Jordan threshold `p = 1/2`; the linear-mode coefficient is `-p·B(p)`, the odd quadratic-mode
coefficient is `E(p)`, and the even quadratic-mode coefficient is `F(p)/(p(1-p))`.
    cor:fold-gauge-anomaly-bernoulli-p-covariance-explicit-even-odd -/
theorem paper_fold_gauge_anomaly_bernoulli_p_covariance_explicit_even_odd
    (p : ℝ) (_hp0 : 0 < p) (_hp1 : p < 1) (hhalf : p ≠ 1 / 2) :
    (∀ m : ℕ,
      bernoulliPCovarianceOdd p m =
        (-(p * bernoulliPCovarianceB p)) * (-p) ^ (2 * m) +
          (p * (1 - p)) ^ m * bernoulliPCovarianceE p) ∧
    (∀ m : ℕ,
      bernoulliPCovarianceEven p m =
        (-(p * bernoulliPCovarianceB p)) * (-p) ^ (2 * m + 1) +
          (p * (1 - p)) ^ (m + 1) * (bernoulliPCovarianceF p / (p * (1 - p)))) ∧
    ¬ bernoulliPCovarianceJordanThreshold p := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    simp [bernoulliPCovarianceOdd, bernoulliPCovarianceA, bernoulliPCovarianceC0]
  · intro m
    simp [bernoulliPCovarianceEven, bernoulliPCovarianceA, bernoulliPCovarianceC1]
  · exact hhalf

end Omega.Folding
