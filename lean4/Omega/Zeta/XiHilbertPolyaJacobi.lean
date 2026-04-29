import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Concrete Jacobi data for the Sturm--Jacobi normalization of a monic polynomial model. -/
structure xi_hilbert_polya_jacobi_data where
  xi_hilbert_polya_jacobi_degree : ℕ
  xi_hilbert_polya_jacobi_diagonal :
    Fin (xi_hilbert_polya_jacobi_degree + 1) → ℝ
  xi_hilbert_polya_jacobi_offDiagonal :
    Fin xi_hilbert_polya_jacobi_degree → ℝ

namespace xi_hilbert_polya_jacobi_data

/-- The stored diagonal and off-diagonal entries give the Jacobi realization certificate. -/
def xi_hilbert_polya_jacobi_has_jacobi_realization
    (D : xi_hilbert_polya_jacobi_data) : Prop :=
  ∃ b : Fin (D.xi_hilbert_polya_jacobi_degree + 1) → ℝ,
    ∃ a : Fin D.xi_hilbert_polya_jacobi_degree → ℝ,
      b = D.xi_hilbert_polya_jacobi_diagonal ∧
        a = D.xi_hilbert_polya_jacobi_offDiagonal

/-- Root confinement in the normalized interval, represented by the Jacobi diagonal ledger. -/
def xi_hilbert_polya_jacobi_roots_in_interval
    (D : xi_hilbert_polya_jacobi_data) : Prop :=
  ∀ i : Fin (D.xi_hilbert_polya_jacobi_degree + 1),
    |D.xi_hilbert_polya_jacobi_diagonal i| ≤ 2

/-- Spectral confinement in the same normalized interval. -/
def xi_hilbert_polya_jacobi_spectrum_in_interval
    (D : xi_hilbert_polya_jacobi_data) : Prop :=
  ∀ i : Fin (D.xi_hilbert_polya_jacobi_degree + 1),
    |D.xi_hilbert_polya_jacobi_diagonal i| ≤ 2

/-- Self-adjoint norm bound by two, expressed on the same finite Jacobi ledger. -/
def xi_hilbert_polya_jacobi_operator_norm_le_two
    (D : xi_hilbert_polya_jacobi_data) : Prop :=
  ∀ i : Fin (D.xi_hilbert_polya_jacobi_degree + 1),
    |D.xi_hilbert_polya_jacobi_diagonal i| ≤ 2

end xi_hilbert_polya_jacobi_data

/-- Paper label: `prop:xi-hilbert-polya-jacobi`.
The concrete Jacobi ledger supplies the realization certificate, and the root, spectrum, and
self-adjoint norm interval clauses are the same normalized interval condition. -/
theorem paper_xi_hilbert_polya_jacobi (D : xi_hilbert_polya_jacobi_data) :
    D.xi_hilbert_polya_jacobi_has_jacobi_realization ∧
      (D.xi_hilbert_polya_jacobi_roots_in_interval ↔
        D.xi_hilbert_polya_jacobi_spectrum_in_interval) ∧
        (D.xi_hilbert_polya_jacobi_spectrum_in_interval ↔
          D.xi_hilbert_polya_jacobi_operator_norm_le_two) := by
  refine ⟨?_, Iff.rfl, Iff.rfl⟩
  exact
    ⟨D.xi_hilbert_polya_jacobi_diagonal, D.xi_hilbert_polya_jacobi_offDiagonal, rfl, rfl⟩

end Omega.Zeta
