import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- Concrete data for the monic factorization and truncated quotient-ring model. -/
structure xi_time_part62af_hankel_gap_quotient_ring_model_data where
  Pmin : Polynomial ℚ
  R : Polynomial ℚ
  P : Polynomial ℚ
  lambda : ℚ
  monic_R : R.Monic
  factorization : P = Pmin * R

/-- The overfitted Hankel polynomial reconstructed from its minimal part and monic gap factor. -/
noncomputable def xi_time_part62af_hankel_gap_quotient_ring_model_factor
    (D : xi_time_part62af_hankel_gap_quotient_ring_model_data) : Polynomial ℚ :=
  D.Pmin * D.R

/-- Canonical representative of a polynomial class in the quotient by the monic gap factor. -/
noncomputable def xi_time_part62af_hankel_gap_quotient_ring_model_representative
    (D : xi_time_part62af_hankel_gap_quotient_ring_model_data) (f : Polynomial ℚ) :
    Polynomial ℚ :=
  f %ₘ D.R

/-- The induced shift is multiplication by `X - lambda`, followed by monic reduction. -/
noncomputable def xi_time_part62af_hankel_gap_quotient_ring_model_shift
    (D : xi_time_part62af_hankel_gap_quotient_ring_model_data) (f : Polynomial ℚ) :
    Polynomial ℚ :=
  ((X - C D.lambda) * f) %ₘ D.R

/-- Paper-facing statement: monic factorization, unique truncated remainders, and the shift law. -/
def xi_time_part62af_hankel_gap_quotient_ring_model_statement
    (D : xi_time_part62af_hankel_gap_quotient_ring_model_data) : Prop :=
  D.P = xi_time_part62af_hankel_gap_quotient_ring_model_factor D ∧
    (∀ f : Polynomial ℚ,
      ∃! r : Polynomial ℚ,
        (∃ q : Polynomial ℚ, r + D.R * q = f) ∧ r.degree < D.R.degree) ∧
      (∀ f : Polynomial ℚ,
        xi_time_part62af_hankel_gap_quotient_ring_model_shift D f =
          xi_time_part62af_hankel_gap_quotient_ring_model_shift D
            (xi_time_part62af_hankel_gap_quotient_ring_model_representative D f))

/-- thm:xi-time-part62af-hankel-gap-quotient-ring-model -/
theorem paper_xi_time_part62af_hankel_gap_quotient_ring_model
    (D : xi_time_part62af_hankel_gap_quotient_ring_model_data) :
    xi_time_part62af_hankel_gap_quotient_ring_model_statement D := by
  refine ⟨D.factorization, ?_, ?_⟩
  · intro f
    refine ⟨f %ₘ D.R, ?_, ?_⟩
    · refine ⟨⟨f /ₘ D.R, ?_⟩, degree_modByMonic_lt f D.monic_R⟩
      exact modByMonic_add_div f D.monic_R
    · intro r hr
      rcases hr.1 with ⟨q, hq⟩
      exact (div_modByMonic_unique q r D.monic_R ⟨hq, hr.2⟩).2.symm
  · intro f
    have hrep :
        (f %ₘ D.R) %ₘ D.R = f %ₘ D.R :=
      (modByMonic_eq_self_iff D.monic_R).mpr (degree_modByMonic_lt f D.monic_R)
    calc
      xi_time_part62af_hankel_gap_quotient_ring_model_shift D f =
          (((X - C D.lambda) %ₘ D.R) * (f %ₘ D.R)) %ₘ D.R := by
            exact mul_modByMonic (X - C D.lambda) f D.R
      _ = (((X - C D.lambda) %ₘ D.R) * ((f %ₘ D.R) %ₘ D.R)) %ₘ D.R := by
            rw [hrep]
      _ = xi_time_part62af_hankel_gap_quotient_ring_model_shift D
            (xi_time_part62af_hankel_gap_quotient_ring_model_representative D f) := by
            unfold xi_time_part62af_hankel_gap_quotient_ring_model_shift
              xi_time_part62af_hankel_gap_quotient_ring_model_representative
            exact (mul_modByMonic (X - C D.lambda) (f %ₘ D.R) D.R).symm

end Omega.Zeta
