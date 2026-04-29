import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Omega.Zeta

noncomputable section

/-- Closed coefficient in the even Taylor expansion of the scale-coherence kernel. -/
def xi_scale_coherence_kernel_zeta_taylor_closedCoefficient
    (zetaEven : ℕ → ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) /
    ((2 : ℝ) ^ (2 * n + 1) * Real.pi ^ (2 * n + 2)) * zetaEven n

/-- Paper-facing statement of the zeta Taylor package: the even coefficients have the displayed
closed form, the even derivatives are the corresponding Taylor coefficients times `(2n)!`, and
the collision constants are generated from those coefficients. -/
def xi_scale_coherence_kernel_zeta_taylor_statement
    (coefficient evenDerivativeAtZero zetaEven : ℕ → ℝ)
    (hankelConstant : ℕ → ℝ) (hankelFromCoefficients : (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  (∀ n,
    coefficient n =
      xi_scale_coherence_kernel_zeta_taylor_closedCoefficient zetaEven n) ∧
    (∀ n,
      evenDerivativeAtZero n =
        (Nat.factorial (2 * n) : ℝ) *
          xi_scale_coherence_kernel_zeta_taylor_closedCoefficient zetaEven n) ∧
      ∀ k, hankelConstant k = hankelFromCoefficients coefficient k

/-- Paper label: `prop:xi-scale-coherence-kernel-zeta-taylor`. -/
theorem paper_xi_scale_coherence_kernel_zeta_taylor
    (coefficient evenDerivativeAtZero zetaEven : ℕ → ℝ)
    (hankelConstant : ℕ → ℝ) (hankelFromCoefficients : (ℕ → ℝ) → ℕ → ℝ)
    (hcoefficient_eval :
      ∀ n,
        coefficient n =
          xi_scale_coherence_kernel_zeta_taylor_closedCoefficient zetaEven n)
    (hderivative_eval :
      ∀ n, evenDerivativeAtZero n = (Nat.factorial (2 * n) : ℝ) * coefficient n)
    (hhankel_eval : ∀ k, hankelConstant k = hankelFromCoefficients coefficient k) :
    xi_scale_coherence_kernel_zeta_taylor_statement
      coefficient evenDerivativeAtZero zetaEven hankelConstant hankelFromCoefficients := by
  refine ⟨hcoefficient_eval, ?_, hhankel_eval⟩
  intro n
  rw [hderivative_eval, hcoefficient_eval]

end

end Omega.Zeta
