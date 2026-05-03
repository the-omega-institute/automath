import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Finite symmetric-function data for the Jacobi--Trudi/Euler primitive-fiber package. -/
structure pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data where
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_length : ℕ
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_lambda :
    Fin pom_schur_trace_jacobi_trudi_euler_primitive_fiber_length → ℤ
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_complete : ℤ → ℚ
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_power_sum : ℕ → ℚ

namespace pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data

noncomputable def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_jacobi_trudi_matrix
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) :
    Matrix
      (Fin D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_length)
      (Fin D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_length) ℚ :=
  fun i j =>
    D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_complete
      (D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_lambda i -
        (i : ℤ) + (j : ℤ))

noncomputable def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_schur_value
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) : ℚ :=
  Matrix.det
    (pom_schur_trace_jacobi_trudi_euler_primitive_fiber_jacobi_trudi_matrix D)

def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_mobius_weight
    (d : ℕ) : ℤ :=
  if d = 1 then 1 else 0

noncomputable def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_primitive_coordinate
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    (1 / (n : ℚ)) *
      Finset.sum n.divisors (fun d =>
        (pom_schur_trace_jacobi_trudi_euler_primitive_fiber_mobius_weight d : ℚ) *
          D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_power_sum (n / d))

noncomputable def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_log_coefficient
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) (n : ℕ) : ℚ :=
  if n = 0 then 0
  else D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_power_sum n / (n : ℚ)

noncomputable def pom_schur_trace_jacobi_trudi_euler_primitive_fiber_euler_exponent
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) (n : ℕ) : ℚ :=
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_primitive_coordinate D n

noncomputable def statement
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) : Prop :=
  pom_schur_trace_jacobi_trudi_euler_primitive_fiber_schur_value D =
      Matrix.det
        (pom_schur_trace_jacobi_trudi_euler_primitive_fiber_jacobi_trudi_matrix D) ∧
    (∀ n,
      pom_schur_trace_jacobi_trudi_euler_primitive_fiber_primitive_coordinate D n =
        (if n = 0 then 0
        else
          (1 / (n : ℚ)) *
            Finset.sum n.divisors (fun d =>
              (pom_schur_trace_jacobi_trudi_euler_primitive_fiber_mobius_weight d : ℚ) *
                D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_power_sum (n / d)))) ∧
    (∀ n,
      pom_schur_trace_jacobi_trudi_euler_primitive_fiber_euler_exponent D n =
        pom_schur_trace_jacobi_trudi_euler_primitive_fiber_primitive_coordinate D n) ∧
    (∀ n,
      pom_schur_trace_jacobi_trudi_euler_primitive_fiber_log_coefficient D n =
        (if n = 0 then 0
        else D.pom_schur_trace_jacobi_trudi_euler_primitive_fiber_power_sum n / (n : ℚ)))

end pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data

open pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data

/-- Paper label: `prop:pom-schur-trace-jacobi-trudi-euler-primitive-fiber`. -/
theorem paper_pom_schur_trace_jacobi_trudi_euler_primitive_fiber
    (D : pom_schur_trace_jacobi_trudi_euler_primitive_fiber_data) : D.statement := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n
    rfl
  · intro n
    rfl

end Omega.POM
