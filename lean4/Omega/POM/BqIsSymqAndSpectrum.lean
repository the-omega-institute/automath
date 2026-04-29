import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Graph.TransferMatrix
import Omega.Zeta.XiBqPowerEntrywiseFibonacciBinomial

namespace Omega.POM

noncomputable section

/-- The `j`-th homogeneous-spectrum term for `Sym^q(M)` written directly from the eigenvalues
`φ` and `φ̄ = (1 - √5) / 2`. -/
def pom_bq_is_symq_and_spectrum_symq_eigenvalue (q : ℕ) (j : Fin (q + 1)) : ℝ :=
  Real.goldenRatio ^ (q - j.1) * Real.goldenConj ^ j.1

/-- The same eigenvalue written in the closed form `(-1)^j φ^(q-2j)`, avoiding integer powers by
keeping the denominator `φ^j` explicit. -/
def pom_bq_is_symq_and_spectrum_closed_eigenvalue (q : ℕ) (j : Fin (q + 1)) : ℝ :=
  ((-1 : ℝ) ^ j.1 * Real.goldenRatio ^ (q - j.1)) / Real.goldenRatio ^ j.1

/-- Concrete paper-facing package: the golden matrix has the expected quadratic characteristic
polynomial, the `Sym^q` action on the monomial basis has the binomial/Fibonacci coefficient rule,
and the resulting spectrum is the standard `φ^(q-j) φ̄^j = (-1)^j φ^(q-2j)` family. -/
def pom_bq_is_symq_and_spectrum_statement (q : ℕ) : Prop :=
  Omega.Graph.goldenMeanAdjacency.charpoly = Polynomial.X ^ 2 - Polynomial.X - 1 ∧
    (∀ k l : ℕ, Omega.Zeta.xiBqPowerEntrywiseFormula q 1 k l) ∧
    ∀ j : Fin (q + 1),
      pom_bq_is_symq_and_spectrum_symq_eigenvalue q j =
        pom_bq_is_symq_and_spectrum_closed_eigenvalue q j

private lemma pom_bq_is_symq_and_spectrum_golden_conj_closed_form (q : ℕ) (j : Fin (q + 1)) :
    pom_bq_is_symq_and_spectrum_symq_eigenvalue q j =
      pom_bq_is_symq_and_spectrum_closed_eigenvalue q j := by
  have hconj : Real.goldenConj = -((Real.goldenRatio : ℝ)⁻¹) := by
    have hinv : (Real.goldenRatio : ℝ)⁻¹ = -Real.goldenConj := by
      simpa using Real.inv_goldenRatio
    linarith
  unfold pom_bq_is_symq_and_spectrum_symq_eigenvalue
  unfold pom_bq_is_symq_and_spectrum_closed_eigenvalue
  rw [hconj]
  rw [show -((Real.goldenRatio : ℝ)⁻¹) = (-1 : ℝ) * (Real.goldenRatio : ℝ)⁻¹ by ring]
  rw [mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- Paper label: `prop:pom-bq-is-symq-and-spectrum`. -/
theorem paper_pom_bq_is_symq_and_spectrum (q : ℕ) :
    pom_bq_is_symq_and_spectrum_statement q := by
  refine ⟨Omega.Graph.goldenMeanAdjacency_charpoly, ?_, ?_⟩
  · intro k l
    exact Omega.Zeta.paper_xi_bq_power_entrywise_fibonacci_binomial q 1 k l
  · intro j
    exact pom_bq_is_symq_and_spectrum_golden_conj_closed_form q j

end

end Omega.POM
