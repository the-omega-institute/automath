import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Folding.KilloPrimeWeightedEllipticFingerprintClt

namespace Omega.Folding

open KilloPrimeWeightedEllipticFingerprintCltData

noncomputable section

/-- The unit-direction parametrization `u(θ) = (cos θ, sin θ)` used for the angular law on `S¹`. -/
def killo_prime_weighted_angular_law_sigma_recovery_unit_direction (θ : ℝ) : Fin 2 → ℝ
  | ⟨0, _⟩ => Real.cos θ
  | ⟨1, _⟩ => Real.sin θ

/-- The quadratic form of a candidate covariance along the unit direction `u(θ)`. -/
def killo_prime_weighted_angular_law_sigma_recovery_directional_quadratic
    (paper_killo_prime_weighted_angular_law_sigma_recovery_covariance : Fin 2 → Fin 2 → ℝ)
    (θ : ℝ) : ℝ :=
  paper_killo_prime_weighted_elliptic_fingerprint_clt_quadratic_form
    paper_killo_prime_weighted_angular_law_sigma_recovery_covariance
    (killo_prime_weighted_angular_law_sigma_recovery_unit_direction θ)

/-- The angular density template determined by the limiting covariance along `S¹`. -/
def killo_prime_weighted_angular_law_sigma_recovery_density
    (paper_killo_prime_weighted_angular_law_sigma_recovery_covariance : Fin 2 → Fin 2 → ℝ) :
    ℝ → ℝ :=
  fun θ =>
    (2 * Real.pi)⁻¹ *
      (killo_prime_weighted_angular_law_sigma_recovery_directional_quadratic
        paper_killo_prime_weighted_angular_law_sigma_recovery_covariance θ)⁻¹

/-- The sigma-recovery statement attached to the limiting covariance from the elliptic CLT
package: the Gaussian limit produces an angular density on `S¹`, and among covariance kernels
with trace `1`, that density determines the limiting covariance uniquely. -/
def killo_prime_weighted_angular_law_sigma_recovery_statement
    (D : KilloPrimeWeightedEllipticFingerprintCltData) : Prop :=
  D.Conclusion ∧
    ∀ paper_killo_prime_weighted_angular_law_sigma_recovery_covariance : Fin 2 → Fin 2 → ℝ,
      (∀ θ : ℝ,
        killo_prime_weighted_angular_law_sigma_recovery_density
            paper_killo_prime_weighted_angular_law_sigma_recovery_covariance θ =
          killo_prime_weighted_angular_law_sigma_recovery_density
            D.paper_killo_prime_weighted_elliptic_fingerprint_clt_limit_covariance θ) →
      (paper_killo_prime_weighted_angular_law_sigma_recovery_covariance ⟨0, by decide⟩ ⟨0, by decide⟩ +
          paper_killo_prime_weighted_angular_law_sigma_recovery_covariance ⟨1, by decide⟩ ⟨1, by decide⟩ =
        1) →
      paper_killo_prime_weighted_angular_law_sigma_recovery_covariance =
        D.paper_killo_prime_weighted_elliptic_fingerprint_clt_limit_covariance

/-- Paper label: `cor:killo-prime-weighted-angular-law-sigma-recovery`. The requested Lean
artifact is a proposition-valued corollary: it packages the angular pushforward law coming from
the elliptic CLT together with the uniqueness statement for recovering the normalized covariance
from its angular density. This is a `def` rather than a `theorem` because the requested
declaration has value type `Prop`. -/
def paper_killo_prime_weighted_angular_law_sigma_recovery
    (D : Omega.Folding.KilloPrimeWeightedEllipticFingerprintCltData) : Prop := by
  exact killo_prime_weighted_angular_law_sigma_recovery_statement D

end

end Omega.Folding
