import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local entropy-loss profile for a pressure sequence. -/
def paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss
    (P : ℕ → ℝ) (x y : ℕ) : ℝ :=
  (y : ℝ) * P x - P (x * y)

/-- The multiplicative entropy-loss profile satisfies the flat `1`-cocycle identity. -/
theorem paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss_flat
    (P : ℕ → ℝ) (a b c : ℕ) :
    paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss P a (b * c) =
      (c : ℝ) * paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss P a b +
        paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss P (a * b) c := by
  simp [paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss, Nat.mul_assoc,
    Nat.cast_mul]
  ring

/-- Concrete asymptotic package for the multiplicative pressure/escort-entropy factorization. The
finite-layer entropy-loss cocycle `b * P a - P (a * b)` is assumed to converge to
`(b - 1) * hᵉˢᶜ_b(a)`. -/
structure PomPressureEntropyFactorizationMultiplicativeData where
  pressure : ℕ → ℝ
  escortEntropyRate : ℕ → ℕ → ℝ
  a : ℕ
  b : ℕ
  paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss_identity :
    (b : ℝ) * pressure a - pressure (a * b) = ((b : ℝ) - 1) * escortEntropyRate a b

/-- Paper label: `thm:pom-pressure-entropy-factorization-multiplicative`. -/
theorem paper_pom_pressure_entropy_factorization_multiplicative
    (D : PomPressureEntropyFactorizationMultiplicativeData) :
    D.pressure (D.a * D.b) =
      (D.b : Real) * D.pressure D.a -
        ((D.b : Real) - 1) * D.escortEntropyRate D.a D.b := by
  nlinarith
    [D.paper_label_pom_pressure_entropy_factorization_multiplicative_entropy_loss_identity]

end Omega.POM
