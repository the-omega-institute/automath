import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Simple-pole Laurent model at the critical point `z = 1 / 3`. -/
def conclusion_relative_zeta_quotient_critical_order_invariance_laurent
    (residue regular : ℂ) (z : ℂ) : ℂ :=
  residue / (1 - 3 * z) + regular

/-- Dividing by the analytic nonvanishing factor is modeled by dividing by its value at `z = 1/3`.
-/
def conclusion_relative_zeta_quotient_critical_order_invariance_relative
    (residue regular zetaMAtThird : ℂ) (z : ℂ) : ℂ :=
  conclusion_relative_zeta_quotient_critical_order_invariance_laurent residue regular z /
    zetaMAtThird

/-- In this Laurent model, the critical pole order is exactly the indicator of a nonzero residue.
-/
def conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder (residue : ℂ) : ℕ :=
  if residue = 0 then 0 else 1

/-- The residue rescales by the inverse analytic factor. -/
def conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
    (residue zetaMAtThird : ℂ) : ℂ :=
  residue / zetaMAtThird

/-- Paper label: `thm:conclusion-relative-zeta-quotient-critical-order-invariance`. Modeling
`ζ_B` by a simple-pole Laurent expansion and `ζ_M` by its nonzero value at `z = 1 / 3`, dividing
by the analytic factor leaves the pole order unchanged and rescales the residue by
`ζ_M(1 / 3)⁻¹`. -/
theorem paper_conclusion_relative_zeta_quotient_critical_order_invariance
    (residue regular zetaMAtThird : ℂ)
    (hResidue : residue ≠ 0) (hzetaM : zetaMAtThird ≠ 0) :
    (∀ z,
      conclusion_relative_zeta_quotient_critical_order_invariance_relative
          residue regular zetaMAtThird z =
        conclusion_relative_zeta_quotient_critical_order_invariance_laurent
          (conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
            residue zetaMAtThird)
          (regular / zetaMAtThird) z) ∧
      conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder
          (conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
            residue zetaMAtThird) =
        conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder residue ∧
      conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder residue = 1 ∧
      conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder
          (conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
            residue zetaMAtThird) = 1 ∧
      conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
          residue zetaMAtThird = residue / zetaMAtThird := by
  have hRescaled :
      conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue
          residue zetaMAtThird ≠ 0 := by
    simpa [conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue] using
      (div_ne_zero hResidue hzetaM)
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro z
    simp [conclusion_relative_zeta_quotient_critical_order_invariance_relative,
      conclusion_relative_zeta_quotient_critical_order_invariance_laurent,
      conclusion_relative_zeta_quotient_critical_order_invariance_rescaledResidue,
      div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc]
  · simp [conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder, hResidue,
      hRescaled]
  · simp [conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder, hResidue]
  · simp [conclusion_relative_zeta_quotient_critical_order_invariance_poleOrder,
      hRescaled]

end

end Omega.Conclusion
