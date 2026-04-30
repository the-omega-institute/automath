import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for comparing two projective output-bucket realizations.  The shared-bucket
predicate below is defined from the two concrete bucket kernels, while the realization fields record
that each moment tower is obtained from its own bucket tower and that equal moment kernels transport
the Perron/log rates. -/
structure xi_projective_output_bucket_determines_integer_moment_tower_data where
  xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel :
    ℕ → Matrix (Fin 2) (Fin 2) ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel' :
    ℕ → Matrix (Fin 2) (Fin 2) ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_momentKernel :
    ℕ → Matrix (Fin 2) (Fin 2) ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' :
    ℕ → Matrix (Fin 2) (Fin 2) ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_perronRate : ℕ → ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_perronRate' : ℕ → ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_logRate : ℕ → ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_logRate' : ℕ → ℝ
  xi_projective_output_bucket_determines_integer_moment_tower_momentKernel_realizes :
    ∀ q : ℕ, 2 ≤ q →
      xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
        xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel q
  xi_projective_output_bucket_determines_integer_moment_tower_momentKernel'_realizes :
    ∀ q : ℕ, 2 ≤ q →
      xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q =
        xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel' q
  xi_projective_output_bucket_determines_integer_moment_tower_perronRate_respects :
    ∀ q : ℕ, 2 ≤ q →
      xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
        xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q →
      xi_projective_output_bucket_determines_integer_moment_tower_perronRate q =
        xi_projective_output_bucket_determines_integer_moment_tower_perronRate' q
  xi_projective_output_bucket_determines_integer_moment_tower_logRate_respects :
    ∀ q : ℕ, 2 ≤ q →
      xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
        xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q →
      xi_projective_output_bucket_determines_integer_moment_tower_logRate q =
        xi_projective_output_bucket_determines_integer_moment_tower_logRate' q

/-- The concrete assertion that the two bucketed output kernels agree at every integer moment level
where the theorem is applied. -/
def xi_projective_output_bucket_determines_integer_moment_tower_data.xi_projective_output_bucket_determines_integer_moment_tower_sameBuckets
    (D : xi_projective_output_bucket_determines_integer_moment_tower_data) : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    D.xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel q =
      D.xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel' q

/-- Paper label: `thm:xi-projective-output-bucket-determines-integer-moment-tower`. -/
theorem paper_xi_projective_output_bucket_determines_integer_moment_tower
    (D : xi_projective_output_bucket_determines_integer_moment_tower_data) :
    D.xi_projective_output_bucket_determines_integer_moment_tower_sameBuckets →
      ∀ q : ℕ, 2 ≤ q →
        D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
            D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q ∧
          D.xi_projective_output_bucket_determines_integer_moment_tower_perronRate q =
            D.xi_projective_output_bucket_determines_integer_moment_tower_perronRate' q ∧
          D.xi_projective_output_bucket_determines_integer_moment_tower_logRate q =
            D.xi_projective_output_bucket_determines_integer_moment_tower_logRate' q := by
  intro hBuckets q hq
  have hMoment :
      D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
        D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q := by
    calc
      D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel q =
          D.xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel q :=
        D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel_realizes q hq
      _ =
          D.xi_projective_output_bucket_determines_integer_moment_tower_outputBucketKernel' q :=
        hBuckets q hq
      _ =
          D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel' q :=
        (D.xi_projective_output_bucket_determines_integer_moment_tower_momentKernel'_realizes
          q hq).symm
  exact
    ⟨hMoment,
      D.xi_projective_output_bucket_determines_integer_moment_tower_perronRate_respects
        q hq hMoment,
      D.xi_projective_output_bucket_determines_integer_moment_tower_logRate_respects
        q hq hMoment⟩

end Omega.Zeta
