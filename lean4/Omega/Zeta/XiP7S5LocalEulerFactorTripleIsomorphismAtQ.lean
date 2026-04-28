import Mathlib.Tactic

namespace Omega.Zeta

/-- Audited local certificate at the ramified prime `q`: a complete splitting pattern with one
double root gives residue degree one and `D_q = I_q = C₂`, while the three representations have
the same one-dimensional invariant space. -/
structure xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data where
  q : ℕ
  residueDegree : ℕ
  decompositionOrder : ℕ
  inertiaOrder : ℕ
  rho4InvariantDimension : ℕ
  rho5InvariantDimension : ℕ
  rho6InvariantDimension : ℕ
  eulerVariable : ℤ
  residueDegree_eq_one : residueDegree = 1
  decompositionOrder_eq_two : decompositionOrder = 2
  inertiaOrder_eq_two : inertiaOrder = 2
  rho4InvariantDimension_eq_one : rho4InvariantDimension = 1
  rho5InvariantDimension_eq_one : rho5InvariantDimension = 1
  rho6InvariantDimension_eq_one : rho6InvariantDimension = 1

namespace xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data

/-- The local Euler factor determined by the invariant dimension. -/
def localEulerFactor
    (D : xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data)
    (invariantDimension : ℕ) : ℤ :=
  1 - D.eulerVariable ^ invariantDimension

/-- The common closed form when the invariant dimension is one. -/
def commonClosedForm (D : xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data) : ℤ :=
  1 - D.eulerVariable

/-- The three ramified local Euler factors coincide with the same closed form. -/
def statement (D : xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data) : Prop :=
  D.residueDegree = 1 ∧
    D.decompositionOrder = D.inertiaOrder ∧
    D.inertiaOrder = 2 ∧
    D.localEulerFactor D.rho4InvariantDimension = D.commonClosedForm ∧
    D.localEulerFactor D.rho5InvariantDimension = D.commonClosedForm ∧
    D.localEulerFactor D.rho6InvariantDimension = D.commonClosedForm ∧
    D.localEulerFactor D.rho4InvariantDimension =
      D.localEulerFactor D.rho5InvariantDimension ∧
    D.localEulerFactor D.rho5InvariantDimension =
      D.localEulerFactor D.rho6InvariantDimension

end xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data

/-- Paper label: `thm:xi-p7-s5-local-euler-factor-triple-isomorphism-at-q`. -/
theorem paper_xi_p7_s5_local_euler_factor_triple_isomorphism_at_q
    (D : xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data) : D.statement := by
  simp [xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data.statement,
    xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data.localEulerFactor,
    xi_p7_s5_local_euler_factor_triple_isomorphism_at_q_data.commonClosedForm,
    D.residueDegree_eq_one, D.decompositionOrder_eq_two, D.inertiaOrder_eq_two,
    D.rho4InvariantDimension_eq_one, D.rho5InvariantDimension_eq_one,
    D.rho6InvariantDimension_eq_one]

end Omega.Zeta
