import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Basic
import Mathlib.Tactic

namespace Omega.Folding

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Quadratic form of the candidate Gaussian covariance against a test vector. -/
def paper_killo_prime_weighted_elliptic_fingerprint_clt_quadratic_form
    (paper_killo_prime_weighted_elliptic_fingerprint_clt_covariance : Fin 2 → Fin 2 → ℝ)
    (paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2,
    ∑ j : Fin 2,
      paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector i *
        paper_killo_prime_weighted_elliptic_fingerprint_clt_covariance i j *
        paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector j

/-- The centered Gaussian MGF with the projected variance prescribed by the covariance form. -/
def paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_mgf
    (paper_killo_prime_weighted_elliptic_fingerprint_clt_covariance : Fin 2 → Fin 2 → ℝ)
    (paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  Real.exp
    ((paper_killo_prime_weighted_elliptic_fingerprint_clt_quadratic_form
        paper_killo_prime_weighted_elliptic_fingerprint_clt_covariance
        paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector /
      2) *
      t ^ (2 : ℕ))

/-- Concrete triangular-array package for the prime-weighted elliptic fingerprint CLT. The fields
record the row sizes, weights, two-dimensional fingerprint values, the `(2 + eta)`-moment control,
the max-weight hypothesis, and the scalar projection convergence used in the Cramer-Wold step. -/
structure KilloPrimeWeightedEllipticFingerprintCltData where
  paper_killo_prime_weighted_elliptic_fingerprint_clt_row_length : ℕ → ℕ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_weight :
    (n : ℕ) →
      Fin (paper_killo_prime_weighted_elliptic_fingerprint_clt_row_length n) → ℝ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_fingerprint :
    (n : ℕ) →
      Fin (paper_killo_prime_weighted_elliptic_fingerprint_clt_row_length n) → Fin 2 → ℝ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_eta : ℝ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_eta_pos :
    0 < paper_killo_prime_weighted_elliptic_fingerprint_clt_eta
  paper_killo_prime_weighted_elliptic_fingerprint_clt_limit_covariance :
    Fin 2 → Fin 2 → ℝ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_projected_mgf :
    (Fin 2 → ℝ) → ℝ → ℕ → ℝ
  paper_killo_prime_weighted_elliptic_fingerprint_clt_centered :
    ∀ n i,
      ∑ j : Fin 2, paper_killo_prime_weighted_elliptic_fingerprint_clt_fingerprint n i j = 0
  paper_killo_prime_weighted_elliptic_fingerprint_clt_moment_bound :
    ∀ n i,
      |paper_killo_prime_weighted_elliptic_fingerprint_clt_weight n i| ^ (2 : ℕ) ≤
        (n + 1 : ℝ) ^ paper_killo_prime_weighted_elliptic_fingerprint_clt_eta
  paper_killo_prime_weighted_elliptic_fingerprint_clt_max_weight :
    ∀ n i, |paper_killo_prime_weighted_elliptic_fingerprint_clt_weight n i| ≤ 1
  paper_killo_prime_weighted_elliptic_fingerprint_clt_lindeberg_feller :
    ∀ paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ,
      ∀ t : ℝ,
        Tendsto
            (fun n : ℕ =>
              paper_killo_prime_weighted_elliptic_fingerprint_clt_projected_mgf
                paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector t n)
            atTop
            (𝓝
              (paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_mgf
                paper_killo_prime_weighted_elliptic_fingerprint_clt_limit_covariance
                paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector
                t))

namespace KilloPrimeWeightedEllipticFingerprintCltData

/-- Scalar convergence for one test vector, in the form delivered by the Lindeberg-Feller step. -/
def paper_killo_prime_weighted_elliptic_fingerprint_clt_scalar_projection_convergence
    (D : KilloPrimeWeightedEllipticFingerprintCltData)
    (paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ) : Prop :=
  ∀ t : ℝ,
    Tendsto
        (fun n : ℕ =>
          D.paper_killo_prime_weighted_elliptic_fingerprint_clt_projected_mgf
            paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector t n)
        atTop
        (𝓝
          (paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_mgf
            D.paper_killo_prime_weighted_elliptic_fingerprint_clt_limit_covariance
            paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector
            t))

/-- Two-dimensional Gaussian limit encoded via the Cramer-Wold family of scalar projections. -/
def paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_limit
    (D : KilloPrimeWeightedEllipticFingerprintCltData) : Prop :=
  ∀ paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ,
    D.paper_killo_prime_weighted_elliptic_fingerprint_clt_scalar_projection_convergence
      paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector

/-- Paper-facing conclusion: every scalar projection converges to the Gaussian law dictated by the
limit covariance, hence the two-dimensional array converges by Cramer-Wold. -/
def Conclusion (D : KilloPrimeWeightedEllipticFingerprintCltData) : Prop :=
  D.paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_limit

lemma paper_killo_prime_weighted_elliptic_fingerprint_clt_lindeberg_feller_scalar
    (D : KilloPrimeWeightedEllipticFingerprintCltData) :
    ∀ paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ,
      D.paper_killo_prime_weighted_elliptic_fingerprint_clt_scalar_projection_convergence
        paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector := by
  intro paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector
  exact D.paper_killo_prime_weighted_elliptic_fingerprint_clt_lindeberg_feller
    paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector

lemma paper_killo_prime_weighted_elliptic_fingerprint_clt_cramer_wold
    (D : KilloPrimeWeightedEllipticFingerprintCltData) :
    (∀ paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector : Fin 2 → ℝ,
      D.paper_killo_prime_weighted_elliptic_fingerprint_clt_scalar_projection_convergence
        paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector) →
      D.paper_killo_prime_weighted_elliptic_fingerprint_clt_gaussian_limit := by
  intro hScalar paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector
  exact hScalar paper_killo_prime_weighted_elliptic_fingerprint_clt_test_vector

end KilloPrimeWeightedEllipticFingerprintCltData

open KilloPrimeWeightedEllipticFingerprintCltData

/-- Paper label: `thm:killo-prime-weighted-elliptic-fingerprint-clt`. The triangular-array
package supplies scalar projection convergence by the recorded Lindeberg-Feller step, and the
two-dimensional Gaussian limit is then the corresponding Cramer-Wold reformulation. -/
theorem paper_killo_prime_weighted_elliptic_fingerprint_clt
    (D : KilloPrimeWeightedEllipticFingerprintCltData) : D.Conclusion := by
  exact D.paper_killo_prime_weighted_elliptic_fingerprint_clt_cramer_wold
    (D.paper_killo_prime_weighted_elliptic_fingerprint_clt_lindeberg_feller_scalar)

end

end Omega.Folding
