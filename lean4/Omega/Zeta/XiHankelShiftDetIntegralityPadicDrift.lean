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

/-- Paper label: `cor:xi-hankel-padic-stiffness-drift-dichotomy-badprimes`. -/
theorem paper_xi_hankel_padic_stiffness_drift_dichotomy_badprimes
    (D : xi_hankel_shift_det_integrality_padic_drift_data) :
    (padicValNat D.p
          D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet = 0 →
        ∀ r : ℕ,
          padicValNat D.p
              (D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
                D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^ r) =
            padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_baseDet) ∧
      (0 < padicValNat D.p
          D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet →
        ∀ r s : ℕ, r < s →
          padicValNat D.p
              (D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
                D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^ r) <
            padicValNat D.p
              (D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
                D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^ s)) ∧
      ((∃ r : ℕ,
          D.p ∣ D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
            D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^ r) ↔
        D.p ∣ D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
          D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet) := by
  let _ : Fact D.p.Prime := D.hp
  have hshift_ne :
      D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ≠ 0 := by
    simpa [xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet] using
      D.xi_hankel_shift_det_integrality_padic_drift_hratio
  have hval :
      ∀ r : ℕ,
        padicValNat D.p
            (D.xi_hankel_shift_det_integrality_padic_drift_baseDet *
              D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet ^ r) =
          padicValNat D.p D.xi_hankel_shift_det_integrality_padic_drift_baseDet +
            r * padicValNat D.p
              D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet := by
    intro r
    rw [padicValNat.mul
        D.xi_hankel_shift_det_integrality_padic_drift_hbase
        (pow_ne_zero _ hshift_ne),
      padicValNat.pow _ hshift_ne]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero r
    rw [hval r, hzero, mul_zero, add_zero]
  · intro hpos r s hrs
    rw [hval r, hval s]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hrs hpos) _
  · constructor
    · rintro ⟨r, hr⟩
      cases r with
      | zero =>
          have hbase :
              D.p ∣ D.xi_hankel_shift_det_integrality_padic_drift_baseDet := by
            simpa using hr
          exact dvd_mul_of_dvd_left hbase
            D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet
      | succ r =>
          have hmul := D.hp.out.dvd_mul.mp hr
          rcases hmul with hbase | hpow
          · exact dvd_mul_of_dvd_left hbase
              D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet
          · have hshift :
                D.p ∣ D.xi_hankel_shift_det_integrality_padic_drift_shiftOperatorDet :=
              D.hp.out.dvd_of_dvd_pow hpow
            exact dvd_mul_of_dvd_right hshift
              D.xi_hankel_shift_det_integrality_padic_drift_baseDet
    · intro hbad
      exact ⟨1, by simpa using hbad⟩

end Omega.Zeta
