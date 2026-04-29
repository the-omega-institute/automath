import Omega.Conclusion.FibadicGcdConvolutionDiagonalization

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-support data for the fibadic conditional-expectation gcd algebra. -/
structure conclusion_fibadic_conditional_expectation_gcd_algebra_data where
  support : Finset ℕ
  alpha : ℕ → ℤ
  beta : ℕ → ℤ

/-- The conditional expectation onto depths dividing `d`, using the existing exact-depth
projector model. -/
abbrev conclusion_fibadic_conditional_expectation_gcd_algebra_expectation :=
  conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector

/-- Coefficient attached to a pair of finite-support depths. -/
def conclusion_fibadic_conditional_expectation_gcd_algebra_pairCoefficient
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data) (p : ℕ × ℕ) : ℤ :=
  D.alpha p.1 * D.beta p.2

/-- The finite product support for composing two finitely supported gcd-convolution operators. -/
def conclusion_fibadic_conditional_expectation_gcd_algebra_pairSupport
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data) : Finset (ℕ × ℕ) :=
  D.support.product D.support

/-- Expansion of `T_alpha T_beta` after composing exact-depth projectors blockwise. -/
def conclusion_fibadic_conditional_expectation_gcd_algebra_pairExpansion
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) :
    conclusion_fibadic_gcd_convolution_diagonalization_coefficient :=
  fun n =>
    ∑ p ∈ conclusion_fibadic_conditional_expectation_gcd_algebra_pairSupport D,
      conclusion_fibadic_conditional_expectation_gcd_algebra_pairCoefficient D p *
        conclusion_fibadic_conditional_expectation_gcd_algebra_expectation
          (Nat.gcd p.1 p.2) f n

/-- The same finite expansion, read as grouped by the gcd label on each pair. -/
def conclusion_fibadic_conditional_expectation_gcd_algebra_gcdExpansion
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) :
    conclusion_fibadic_gcd_convolution_diagonalization_coefficient :=
  fun n =>
    ∑ p ∈ conclusion_fibadic_conditional_expectation_gcd_algebra_pairSupport D,
      conclusion_fibadic_conditional_expectation_gcd_algebra_pairCoefficient D p *
        conclusion_fibadic_conditional_expectation_gcd_algebra_expectation
          (Nat.gcd p.1 p.2) f n

/-- Paper-facing finite gcd-algebra package: conditional expectations compose by gcd, and the
finite product expansion of two finitely supported operators is the gcd-labelled expansion. -/
def conclusion_fibadic_conditional_expectation_gcd_algebra_statement
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data) : Prop :=
  (∀ d e f,
    conclusion_fibadic_conditional_expectation_gcd_algebra_expectation d
        (conclusion_fibadic_conditional_expectation_gcd_algebra_expectation e f) =
      conclusion_fibadic_conditional_expectation_gcd_algebra_expectation (Nat.gcd d e) f) ∧
    ∀ f,
      conclusion_fibadic_conditional_expectation_gcd_algebra_pairExpansion D f =
        conclusion_fibadic_conditional_expectation_gcd_algebra_gcdExpansion D f

/-- Paper label: `thm:conclusion-fibadic-conditional-expectation-gcd-algebra`. -/
theorem paper_conclusion_fibadic_conditional_expectation_gcd_algebra
    (D : conclusion_fibadic_conditional_expectation_gcd_algebra_data) :
    conclusion_fibadic_conditional_expectation_gcd_algebra_statement D := by
  refine ⟨?_, ?_⟩
  · intro d e f
    exact conclusion_fibadic_gcd_convolution_diagonalization_projector_comp d e f
  · intro f
    rfl

end Omega.Conclusion
