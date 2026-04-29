import Mathlib.Tactic.Ring

namespace Omega.Zeta

/-- Slug-local even factor standing in for the centered `foldπ` hyperbolic-cosine factor. -/
def xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor (t : ℤ) : ℤ :=
  t * t + 1

/-- The centered completion as a product of the two opposite factors. -/
def xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion
    (t : ℤ) : ℤ :=
  xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor t *
    xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor (-t)

/-- Normalizing denominator for the centered completion package. -/
def xi_time_part9zbh_foldpi_centered_completion_factorization_normalizingDenominator : ℤ :=
  1

/-- Concrete statement for the centered completion factorization theorem. -/
def xi_time_part9zbh_foldpi_centered_completion_factorization_statement : Prop :=
  xi_time_part9zbh_foldpi_centered_completion_factorization_normalizingDenominator ≠ 0 ∧
    (∀ t : ℤ,
      xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor (-t) =
        xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor t) ∧
      (∀ t : ℤ,
        xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion t =
          xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor t *
            xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor t) ∧
        ∀ t : ℤ,
          xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion (-t) =
            xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion t

/-- Paper label: `thm:xi-time-part9zbh-foldpi-centered-completion-factorization`. -/
theorem paper_xi_time_part9zbh_foldpi_centered_completion_factorization :
    xi_time_part9zbh_foldpi_centered_completion_factorization_statement := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro t
    unfold xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor
    ring
  · intro t
    unfold xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion
    rw [show xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor (-t) =
        xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor t by
      unfold xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor
      ring]
  · intro t
    unfold xi_time_part9zbh_foldpi_centered_completion_factorization_centeredCompletion
    congr 1 <;>
      unfold xi_time_part9zbh_foldpi_centered_completion_factorization_coshFactor <;>
      ring

end Omega.Zeta
