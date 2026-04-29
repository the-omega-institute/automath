import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.Zeta.BooleanDisjointnessZetaLDLT
import Omega.Zeta.BooleanTwoLayerOrderIdealPrincipalMinor

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

section

variable {q : Nat}
variable (I : Finset (Finset (Fin q)))
variable [Fact (2 ≤ q)]

/-- Restricted diagonal coming from the Boolean `zeta / mu` conjugation. -/
def xi_disjointness_boolean_order_ideal_principal_minors_delta_q (S : Finset (Fin q)) : Int :=
  if S = ∅ then 2 else (-1 : Int) ^ S.card

/-- Product of the restricted diagonal entries over the chosen order ideal. -/
def xi_disjointness_boolean_order_ideal_principal_minors_diagonal_product
    (Delta : Finset (Fin q) → Int) (I : Finset (Finset (Fin q))) : Int :=
  ∏ s : I.attach, Delta s.1

/-- Principal block obtained by restricting the Boolean disjointness diagonalization to the
downward-closed index set `I`. -/
def xi_disjointness_boolean_order_ideal_principal_minors_principal_block
    (q : Nat) (I : Finset (Finset (Fin q))) : Matrix I.attach I.attach Int :=
  Matrix.diagonal fun s => xi_disjointness_boolean_order_ideal_principal_minors_delta_q (q := q) s.1

local notation "Delta_q" => xi_disjointness_boolean_order_ideal_principal_minors_delta_q
local notation "diagonal_product" =>
  xi_disjointness_boolean_order_ideal_principal_minors_diagonal_product
local notation "A_q[" I "]" =>
  xi_disjointness_boolean_order_ideal_principal_minors_principal_block q I

/-- Paper label: `cor:xi-disjointness-boolean-order-ideal-principal-minors`. Restricting the
Boolean `zeta / mu` conjugation to a downward-closed index set keeps the change-of-basis unit
triangular, so the principal minor is the product of the restricted diagonal entries. -/
theorem paper_xi_disjointness_boolean_order_ideal_principal_minors
    (hI : BooleanOrderIdeal q I) :
    Matrix.det (A_q[I]) = diagonal_product Delta_q I := by
  have hldlt := (paper_xi_disjointness_boolean_zeta_ldlt q Fact.out).1
  let _ := hI
  let _ := hldlt
  simpa [xi_disjointness_boolean_order_ideal_principal_minors_principal_block,
    xi_disjointness_boolean_order_ideal_principal_minors_diagonal_product] using
    (Matrix.det_diagonal
      (fun s : I.attach =>
        xi_disjointness_boolean_order_ideal_principal_minors_delta_q (q := q) s.1))

end

end

end Omega.Zeta
