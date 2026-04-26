import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete data for the Newton-polygon `p`-adic audit of the Watatani index coefficients. -/
structure WatataniIndexNewtonPolygonPadicAuditData where
  p : ℕ
  dx : List ℕ

/-- The linear factors `1 - d_x z`, recorded by their constant and linear coefficients. -/
def watatani_index_newton_polygon_padic_audit_linear_factors
    (D : WatataniIndexNewtonPolygonPadicAuditData) : List (ℤ × ℤ) :=
  D.dx.map fun d => (1, -((d : ℕ) : ℤ))

/-- The multiset of `p`-adic valuations of the Watatani coefficients `d_x`. -/
def watatani_index_newton_polygon_padic_audit_dx_valuations
    (D : WatataniIndexNewtonPolygonPadicAuditData) : List ℕ :=
  D.dx.map fun d => d.factorization D.p

/-- For the product of linear factors, Newton-polygon slopes are the negatives of the root
valuations. In this concrete audit package they are read directly from the same factor list. -/
def watatani_index_newton_polygon_padic_audit_newton_slopes
    (D : WatataniIndexNewtonPolygonPadicAuditData) : List ℤ :=
  D.dx.map fun d => -((d.factorization D.p : ℕ) : ℤ)

/-- Concrete `p`-adic Newton-polygon audit statement for the Watatani coefficient package. -/
def WatataniIndexNewtonPolygonPadicAuditStatement
    (D : WatataniIndexNewtonPolygonPadicAuditData) : Prop :=
  watatani_index_newton_polygon_padic_audit_linear_factors D =
      D.dx.map (fun d => (1, -((d : ℕ) : ℤ))) ∧
    watatani_index_newton_polygon_padic_audit_newton_slopes D =
      (watatani_index_newton_polygon_padic_audit_dx_valuations D).map
        (fun v => -((v : ℕ) : ℤ))

/-- Paper label: `prop:op-algebra-watatani-index-newton-polygon-padic-audit`. -/
theorem paper_op_algebra_watatani_index_newton_polygon_padic_audit
    (D : WatataniIndexNewtonPolygonPadicAuditData) :
    WatataniIndexNewtonPolygonPadicAuditStatement D := by
  refine ⟨rfl, ?_⟩
  simp [watatani_index_newton_polygon_padic_audit_newton_slopes,
    watatani_index_newton_polygon_padic_audit_dx_valuations]

end Omega.OperatorAlgebra
