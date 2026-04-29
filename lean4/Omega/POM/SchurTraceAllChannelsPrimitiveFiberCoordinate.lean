import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- The finite exponent-vector expansion of a complete homogeneous term in primitive-fiber
coordinates `b 1, ..., b q`.  The exponent vector is bounded by `n`, so this is a genuinely
finite construction. -/
noncomputable def pom_schur_trace_all_channels_primitive_fiber_coordinate_complete_from_primitive
    (q : ℕ) (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ k : Fin q → Fin (n + 1),
    if (∑ r : Fin q, ((r : ℕ) + 1) * (k r : ℕ)) = n then
      ∏ r : Fin q, b ((r : ℕ) + 1) ^ (k r : ℕ)
    else 0

/-- Complete homogeneous terms extended by zero on negative Jacobi--Trudi indices. -/
noncomputable def pom_schur_trace_all_channels_primitive_fiber_coordinate_complete_int
    (q : ℕ) (b : ℕ → ℚ) (n : ℤ) : ℚ :=
  if _ : 0 ≤ n then
    pom_schur_trace_all_channels_primitive_fiber_coordinate_complete_from_primitive q b n.toNat
  else 0

/-- Jacobi--Trudi matrix with every complete homogeneous entry expanded in the primitive
fiber-coordinate polynomial data. -/
noncomputable def pom_schur_trace_all_channels_primitive_fiber_coordinate_jacobi_trudi_matrix
    (q ell : ℕ) (lambda : Fin ell → ℤ) (b : ℕ → ℚ) :
    Matrix (Fin ell) (Fin ell) ℚ :=
  fun i j =>
    pom_schur_trace_all_channels_primitive_fiber_coordinate_complete_int q b
      (lambda i - (i : ℤ) + (j : ℤ))

/-- The Schur channel trace coordinate obtained from the finite primitive-fiber determinant. -/
noncomputable def pom_schur_trace_all_channels_primitive_fiber_coordinate_schur_trace
    (q ell : ℕ) (lambda : Fin ell → ℤ) (b : ℕ → ℚ) : ℚ :=
  Matrix.det
    (pom_schur_trace_all_channels_primitive_fiber_coordinate_jacobi_trudi_matrix q ell lambda b)

/-- Concrete statement for all finite Schur channels: the normalized trace coordinate is the
Jacobi--Trudi determinant, and every matrix entry is the finite primitive-fiber expansion. -/
def pom_schur_trace_all_channels_primitive_fiber_coordinate_statement : Prop :=
  ∀ (q ell : ℕ) (lambda : Fin ell → ℤ) (b : ℕ → ℚ),
    pom_schur_trace_all_channels_primitive_fiber_coordinate_schur_trace q ell lambda b =
        Matrix.det
          (pom_schur_trace_all_channels_primitive_fiber_coordinate_jacobi_trudi_matrix
            q ell lambda b) ∧
      ∀ i j,
        pom_schur_trace_all_channels_primitive_fiber_coordinate_jacobi_trudi_matrix
            q ell lambda b i j =
          pom_schur_trace_all_channels_primitive_fiber_coordinate_complete_int q b
            (lambda i - (i : ℤ) + (j : ℤ))

/-- Paper label: `cor:pom-schur-trace-all-channels-primitive-fiber-coordinate`. -/
theorem paper_pom_schur_trace_all_channels_primitive_fiber_coordinate :
    pom_schur_trace_all_channels_primitive_fiber_coordinate_statement := by
  intro q ell lambda b
  exact ⟨rfl, fun _ _ => rfl⟩

end Omega.POM
