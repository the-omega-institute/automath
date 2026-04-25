import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete determinant data for a shifted Hankel package. -/
structure xi_hankel_shift_det_integrality_padic_drift_data where
  p : ℕ
  hp : Fact p.Prime
  xi_hankel_shift_det_integrality_padic_drift_dimension : ℕ
  xi_hankel_shift_det_integrality_padic_drift_shift : ℕ
  xi_hankel_shift_det_integrality_padic_drift_baseDet : ℕ
  xi_hankel_shift_det_integrality_padic_drift_shiftRatio : ℕ
  xi_hankel_shift_det_integrality_padic_drift_hbase :
    xi_hankel_shift_det_integrality_padic_drift_baseDet ≠ 0
  xi_hankel_shift_det_integrality_padic_drift_hratio :
    xi_hankel_shift_det_integrality_padic_drift_shiftRatio ≠ 0

namespace xi_hankel_shift_det_integrality_padic_drift_data

/-- Determinant of the concrete shift operator on the Hankel column space. -/
def xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet
    (D : xi_hankel_shift_det_integrality_padic_drift_data) : ℕ :=
  D.xi_hankel_shift_det_integrality_padic_drift_shiftRatio

/-- Shifted determinant produced from `H_r = H_0 A^r`. -/
def xi_hankel_shift_det_integrality_padic_drift_shiftedDeterminant
    (D : xi_hankel_shift_det_integrality_padic_drift_data) : ℕ :=
  D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
    D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^
      D.xi_hankel_shift_det_integrality_padic_drift_shift

/-- The determinant ratio is integral. -/
def integralDetRatio
    (D : xi_hankel_shift_det_integrality_padic_drift_data) : Prop :=
  ∃ m : ℕ,
    D.xi_hankel_shift_det_integrality_padic_drift_shiftedDeterminant =
      D.xi_hankel_shift_det_integrality_padic_drift_baseDet * m

/-- Geometric determinant law for the shift. -/
def shiftedDeterminantGeometric
    (D : xi_hankel_shift_det_integrality_padic_drift_data) : Prop :=
  D.xi_hankel_shift_det_integrality_padic_drift_shiftedDeterminant =
    D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
      D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^
        D.xi_hankel_shift_det_integrality_padic_drift_shift

/-- Affine `p`-adic drift coming from valuation additivity on the geometric determinant law. -/
def padicDriftAffine
    (D : xi_hankel_shift_det_integrality_padic_drift_data) : Prop :=
  padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_shiftedDeterminant =
    padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_baseDet +
      D.xi_hankel_shift_det_integrality_padic_drift_shift *
        padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet

end xi_hankel_shift_det_integrality_padic_drift_data

open xi_hankel_shift_det_integrality_padic_drift_data

/-- Paper label: `thm:xi-hankel-shift-det-integrality-padic-drift`. -/
theorem paper_xi_hankel_shift_det_integrality_padic_drift
    (D : xi_hankel_shift_det_integrality_padic_drift_data) :
    D.integralDetRatio ∧ D.shiftedDeterminantGeometric ∧ D.padicDriftAffine := by
  let _ : Fact D.p.Prime := D.hp
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^
      D.xi_hankel_shift_det_integrality_padic_drift_shift, rfl⟩
  · rfl
  · have hvaluation :
        padicValNat D.p
            (D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
              D.xi_hankel_shift_det_integrality_padic_drift_shiftRatio ^
                D.xi_hankel_shift_det_integrality_padic_drift_shift) =
          padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_baseDet +
            D.xi_hankel_shift_det_integrality_padic_drift_shift *
              padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_shiftRatio := by
      rw [padicValNat.mul
          D.xi_hankel_shift_det_integrality_padic_drift_hbase
          (pow_ne_zero _ D.xi_hankel_shift_det_integrality_padic_drift_hratio),
        padicValNat.pow _ D.xi_hankel_shift_det_integrality_padic_drift_hratio]
    simpa [padicDriftAffine, xi_hankel_shift_det_integrality_padic_drift_shiftedDeterminant,
      xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet] using hvaluation

end Omega.Zeta
