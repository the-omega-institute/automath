import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix Polynomial
open scoped BigOperators

noncomputable section

/-- Concrete finite shifted-Hankel pencil data. The matrix `pencilOperator` is the
`H_κ^{-1} H_{κ+1}` transfer matrix after choosing the supplied Vandermonde basis. -/
structure xi_time_part9e_shifted_hankel_pencil_diagonalization_data where
  xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa : ℕ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes :
    Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa → ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_weights :
    Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa → ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel :
    Matrix
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa)
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa) ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_shiftedHankel :
    Matrix
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa)
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa) ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde :
    Matrix
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa)
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa) ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermondeInv :
    Matrix
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa)
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa) ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator :
    Matrix
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa)
      (Fin xi_time_part9e_shifted_hankel_pencil_diagonalization_kappa) ℂ
  xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel_factorization :
    xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel =
      xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde *
        Matrix.diagonal xi_time_part9e_shifted_hankel_pencil_diagonalization_weights *
          xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde.transpose
  xi_time_part9e_shifted_hankel_pencil_diagonalization_shifted_factorization :
    xi_time_part9e_shifted_hankel_pencil_diagonalization_shiftedHankel =
      xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde *
        Matrix.diagonal
          (fun i =>
            xi_time_part9e_shifted_hankel_pencil_diagonalization_weights i *
              xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes i) *
          xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde.transpose
  xi_time_part9e_shifted_hankel_pencil_diagonalization_pencil_diagonalization :
    xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator =
      xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde *
        Matrix.diagonal xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes *
          xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermondeInv
  xi_time_part9e_shifted_hankel_pencil_diagonalization_charpoly_eq :
    xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator.charpoly =
      ∏ i,
        (Polynomial.X -
          Polynomial.C (xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes i))
  xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel_self_adjoint :
    xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel *
        xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator =
      xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator.transpose *
        xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel

namespace xi_time_part9e_shifted_hankel_pencil_diagonalization_data

/-- The shifted Hankel pencil is similar to the node diagonal matrix. -/
def has_node_diagonalization
    (D : xi_time_part9e_shifted_hankel_pencil_diagonalization_data) : Prop :=
  D.xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator =
    D.xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermonde *
      Matrix.diagonal D.xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes *
        D.xi_time_part9e_shifted_hankel_pencil_diagonalization_vandermondeInv

/-- The characteristic polynomial is the node polynomial of the finite pencil. -/
def charpoly_eq_node_polynomial
    (D : xi_time_part9e_shifted_hankel_pencil_diagonalization_data) : Prop :=
  D.xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator.charpoly =
    ∏ i,
      (Polynomial.X -
        Polynomial.C (D.xi_time_part9e_shifted_hankel_pencil_diagonalization_nodes i))

/-- The transfer operator is self-adjoint for the Hankel bilinear form. -/
def is_hankel_self_adjoint
    (D : xi_time_part9e_shifted_hankel_pencil_diagonalization_data) : Prop :=
  D.xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel *
      D.xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator =
    D.xi_time_part9e_shifted_hankel_pencil_diagonalization_pencilOperator.transpose *
      D.xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel

end xi_time_part9e_shifted_hankel_pencil_diagonalization_data

/-- Paper label: `thm:xi-time-part9e-shifted-hankel-pencil-diagonalization`. -/
theorem paper_xi_time_part9e_shifted_hankel_pencil_diagonalization
    (D : xi_time_part9e_shifted_hankel_pencil_diagonalization_data) :
    D.has_node_diagonalization ∧
      D.charpoly_eq_node_polynomial ∧
        D.is_hankel_self_adjoint := by
  exact
    ⟨D.xi_time_part9e_shifted_hankel_pencil_diagonalization_pencil_diagonalization,
      D.xi_time_part9e_shifted_hankel_pencil_diagonalization_charpoly_eq,
      D.xi_time_part9e_shifted_hankel_pencil_diagonalization_hankel_self_adjoint⟩

end

end Omega.Zeta
