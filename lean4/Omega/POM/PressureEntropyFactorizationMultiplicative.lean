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

/-- Paper label: `cor:pom-escort-renyi-rate-inversion`. -/
theorem paper_pom_escort_renyi_rate_inversion
    (pressure : ℕ → ℝ) (escortEntropyRate : ℕ → ℕ → ℝ)
    (hfactor :
      ∀ a b, 1 ≤ a → 2 ≤ b →
        pressure (a * b) =
          (b : ℝ) * pressure a - ((b : ℝ) - 1) * escortEntropyRate a b)
    (hP1 : pressure 1 = Real.log 2) :
    (∀ a b, 1 ≤ a → 2 ≤ b →
      escortEntropyRate a b = ((b : ℝ) * pressure a - pressure (a * b)) / ((b : ℝ) - 1)) ∧
    ∀ b, 2 ≤ b →
      escortEntropyRate 1 b = ((b : ℝ) * Real.log 2 - pressure b) / ((b : ℝ) - 1) := by
  have hinv :
      ∀ a b, 1 ≤ a → 2 ≤ b →
        escortEntropyRate a b = ((b : ℝ) * pressure a - pressure (a * b)) / ((b : ℝ) - 1) := by
    intro a b ha hb
    have hb1_ne : (b : ℝ) - 1 ≠ 0 := by
      have hb_ne : b ≠ 1 := by omega
      exact sub_ne_zero.mpr (by exact_mod_cast hb_ne)
    apply (eq_div_iff hb1_ne).2
    nlinarith [hfactor a b ha hb]
  refine ⟨?_, ?_⟩
  · exact hinv
  · intro b hb
    have hmain := hinv 1 b (by omega) hb
    simpa [hP1] using hmain

end Omega.POM
