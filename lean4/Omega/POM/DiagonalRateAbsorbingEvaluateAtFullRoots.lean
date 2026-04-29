import Mathlib.Tactic
import Omega.POM.DiagonalRateAbsorbingWronskianIdentitySecondary

namespace Omega.POM

/-- Concrete data for evaluating the deleted-point Laguerre polynomial at a full-spectrum root. -/
structure pom_diagonal_rate_absorbing_evaluate_at_full_roots_data where
  κ : ℝ
  ty : ℝ
  a : ℝ
  zi : ℝ
  qDelta_root :
    pom_diagonal_rate_absorbing_wronskian_identity_qDelta κ ty a zi = 0
  root_nonzero : zi ≠ 0
  ty_noncollision : ty ≠ zi
  deleted_noncollision : a ≠ zi

namespace pom_diagonal_rate_absorbing_evaluate_at_full_roots_data

/-- Evaluation formula for `Q_{-y}` at a root of `Q_δ`. -/
def pom_diagonal_rate_absorbing_evaluate_at_full_roots_formula
    (D : pom_diagonal_rate_absorbing_evaluate_at_full_roots_data) : Prop :=
  pom_diagonal_rate_absorbing_wronskian_identity_qMinus D.κ D.a D.zi =
    D.zi * pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.zi /
      (D.ty - D.zi) ^ 2

/-- Noncollision forces the deleted-point value at the full-spectrum root to be nonzero. -/
def pom_diagonal_rate_absorbing_evaluate_at_full_roots_nonzero
    (D : pom_diagonal_rate_absorbing_evaluate_at_full_roots_data) : Prop :=
  pom_diagonal_rate_absorbing_wronskian_identity_qMinus D.κ D.a D.zi ≠ 0

end pom_diagonal_rate_absorbing_evaluate_at_full_roots_data

open pom_diagonal_rate_absorbing_evaluate_at_full_roots_data

/-- Paper label: `cor:pom-diagonal-rate-absorbing-evaluate-at-full-roots`. Evaluating the
secondary Wronskian identity at a full-spectrum root makes the `Q_δ` term vanish, leaving an
explicit formula for `Q_{-y}(z_i)`; the noncollision assumptions force the right-hand side to be
nonzero. -/
theorem paper_pom_diagonal_rate_absorbing_evaluate_at_full_roots
    (D : pom_diagonal_rate_absorbing_evaluate_at_full_roots_data) :
    D.pom_diagonal_rate_absorbing_evaluate_at_full_roots_formula ∧
      D.pom_diagonal_rate_absorbing_evaluate_at_full_roots_nonzero := by
  let E : DiagonalRateAbsorbingWronskianIdentitySecondaryData :=
    { κ := D.κ, ty := D.ty, a := D.a, z := D.zi }
  have hwronskian := paper_pom_diagonal_rate_absorbing_wronskian_identity_secondary E
  have hwronskian' :
      (D.ty - D.zi) ^ 2 * pom_diagonal_rate_absorbing_wronskian_identity_qMinus D.κ D.a D.zi =
        D.zi * pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.zi := by
    simpa [E, DiagonalRateAbsorbingWronskianIdentitySecondaryData.secondaryWronskianIdentity,
      D.qDelta_root] using hwronskian
  have hden_ne : (D.ty - D.zi) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr D.ty_noncollision)
  have hformula :
      pom_diagonal_rate_absorbing_wronskian_identity_qMinus D.κ D.a D.zi =
        D.zi * pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.zi /
          (D.ty - D.zi) ^ 2 := by
    apply (eq_div_iff hden_ne).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hwronskian'
  have hpDelta_ne :
      pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.zi ≠ 0 := by
    unfold pom_diagonal_rate_absorbing_wronskian_identity_pDelta
      pom_diagonal_rate_absorbing_wronskian_identity_pMinus
    exact mul_ne_zero (sub_ne_zero.mpr D.ty_noncollision) (sub_ne_zero.mpr D.deleted_noncollision)
  have hnum_ne :
      D.zi * pom_diagonal_rate_absorbing_wronskian_identity_pDelta D.ty D.a D.zi ≠ 0 :=
    mul_ne_zero D.root_nonzero hpDelta_ne
  refine ⟨hformula, ?_⟩
  dsimp [pom_diagonal_rate_absorbing_evaluate_at_full_roots_nonzero]
  rw [hformula]
  exact div_ne_zero hnum_ne hden_ne

end Omega.POM
